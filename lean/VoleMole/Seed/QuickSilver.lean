import VoleMole.SeedExtraction

/-!
# Lemma L4: QuickSilver with `chall₂`-dependent constraints (sketch, Claim 3)

Paper proof: `lean/docs/extraction/L4-quicksilver.md`. This file formalizes the deterministic and counting
cores of L4.

1. **Top coefficient** (`QSExpr`, `QSExpr.eval_natDegree_coeff`, `checkPoly_natDegree_coeff`):
   the verifier's QuickSilver computation is a circuit of `+`, `×`, public constants at a degree
   and degree raisings over the MACs. On the accepting set, every witness MAC is
   `q_j(Δ) = V*_j + w*_j·Δ` (L3, after the correction `d`). Each constraint then becomes a
   polynomial `p_k ∈ F[X]` of degree `≤ d` whose `X^d` coefficient is the constraint value
   `f_k(w*)`. The verifier's check value is `Σ_k χ_k p_k(Δ) + R(Δ)`, where `R` collects the
   masks, the prover's `ã_i` and the prover's check value. `R` has degree `≤ d − 1`
   (`maskPoly_natDegree_le`), so the `X^d` coefficient of the check polynomial is
   `Σ_k χ_k f_k(w*)`. No sign or scaling appears, since the field has characteristic 2.
2. **ZKHash as implemented** (`blockedHash_eq_sum`, `horner_eq_sum`, `zkHash_eq_code`,
   `zkHash_eq_sum`, `card_zk_bad_le`, `zkHash_prob_le`): with
   `chall₂ = (r₀, r₁, s, t)`, where `t` ranges over a subset `S` (the 64-bit polynomials),
   `χ_k = r₀ s^{n−1−k} + r₁ t^{n−1−k}`. For `f ≠ 0`, at most a
   `1/|F| + (n−1)²/(|F|·|S|)` fraction of challenges give `Σ_k χ_k f_k = 0`.
3. **`chall₂`-dependent constraints** (`card_combined_bad_le`, `combined_prob_le`): one constraint
   slot `k₀` holds the combination `Σ_m l_m a_m(w*)`. Over the product of the QuickSilver
   challenge and an independent uniform `l`, the event "some uncombined constraint fails but
   `Σ_k χ_k f_k(w*; l) = 0`" has probability at most `ε_QS + 1/|F|`.
4. **Glue to `SeedExtraction`** (`claim3_of_good`, `bits_of_bit_constraints`): on a good
   challenge, either every uncombined constraint holds or `|A| ≤ d`, which is `hclaim3` of
   `extraction_cases`. The bit constraints give `hbits` in characteristic 2.
-/

open Finset Polynomial

set_option linter.unusedSectionVars false

namespace VoleMole.Seed

/-! ## 1. The verifier's QuickSilver circuit and its top coefficient -/

/-- A QuickSilver circuit over witness rows `ι`, as built by the relations' `constraints` code
from faest-arch-opt's operations. Each node has a formal degree `deg`.
* `input j`: the committed witness bit `j` (`get_witness_bit`), of degree 1.
* `const c e`: a public constant `c` at degree `e`. The verifier's MAC is `c·Δ^e`.
* `add a b`: a sum of two values of the same degree.
* `mul a b`: a product, whose degree is the sum of the degrees. A product with a public constant is
  `mul (const c 0) a`, and `combine_8_bits` is a sum of such products.
* `raise k a`: lifting a value from degree `e` to degree `e + k`. The verifier multiplies its MAC by
  `Δ^k`. -/
inductive QSExpr (F ι : Type*) : Type _
  | input : ι → QSExpr F ι
  | const : F → ℕ → QSExpr F ι
  | add : QSExpr F ι → QSExpr F ι → QSExpr F ι
  | mul : QSExpr F ι → QSExpr F ι → QSExpr F ι
  | raise : ℕ → QSExpr F ι → QSExpr F ι

namespace QSExpr

variable {F ι : Type*}

/-- The formal degree, as tracked by the C++ template parameter `deg`. -/
def deg : QSExpr F ι → ℕ
  | input _ => 1
  | const _ e => e
  | add a _ => deg a
  | mul a b => deg a + deg b
  | raise k a => deg a + k

/-- Well-formedness: sums are of values of equal degree (enforced by the C++ types). -/
def WF : QSExpr F ι → Prop
  | input _ => True
  | const _ _ => True
  | add a b => WF a ∧ WF b ∧ deg a = deg b
  | mul a b => WF a ∧ WF b
  | raise _ a => WF a

variable [Field F]

/-- The verifier's MAC as a polynomial in `Δ`, given the witness MAC polynomials `q`. Evaluating
at `Δ` gives what the verifier computes, since all its operations are ring operations. -/
noncomputable def eval (q : ι → F[X]) : QSExpr F ι → F[X]
  | input j => q j
  | const c e => C c * X ^ e
  | add a b => eval q a + eval q b
  | mul a b => eval q a * eval q b
  | raise k a => eval q a * X ^ k

/-- The constraint value: the circuit evaluated on `w ∈ F^ι`, with constants as themselves and
raisings as the identity. -/
def value (w : ι → F) : QSExpr F ι → F
  | input j => w j
  | const c _ => c
  | add a b => value w a + value w b
  | mul a b => value w a * value w b
  | raise _ a => value w a

/-- **The top coefficient is the constraint value.** If every witness MAC is affine in `Δ` with
slope `w_j` (L3 plus the correction: `q_j = V*_j + w*_j·X`), then a well-formed circuit of formal
degree `e` evaluates to a polynomial of degree `≤ e` whose `X^e` coefficient is its value at `w`. -/
theorem eval_natDegree_coeff (q : ι → F[X]) (w : ι → F)
    (hq : ∀ j, (q j).natDegree ≤ 1 ∧ (q j).coeff 1 = w j) :
    ∀ E : QSExpr F ι, E.WF → (eval q E).natDegree ≤ E.deg ∧ (eval q E).coeff E.deg = value w E
  | input j, _ => hq j
  | const c e, _ => by
      refine ⟨natDegree_C_mul_X_pow_le c e, ?_⟩
      simp [eval, deg, value]
  | add a b, ⟨ha, hb, hab⟩ => by
      obtain ⟨da, ca⟩ := eval_natDegree_coeff q w hq a ha
      obtain ⟨db, cb⟩ := eval_natDegree_coeff q w hq b hb
      refine ⟨(natDegree_add_le _ _).trans (max_le da (hab ▸ db)), ?_⟩
      simp only [eval, deg, value, coeff_add]
      rw [ca, hab, cb]
  | mul a b, ⟨ha, hb⟩ => by
      obtain ⟨da, ca⟩ := eval_natDegree_coeff q w hq a ha
      obtain ⟨db, cb⟩ := eval_natDegree_coeff q w hq b hb
      refine ⟨natDegree_mul_le_of_le da db, ?_⟩
      simp only [eval, deg, value]
      rw [coeff_mul_add_eq_of_natDegree_le da db, ca, cb]
  | raise k a, ha => by
      obtain ⟨da, ca⟩ := eval_natDegree_coeff q w hq a ha
      refine ⟨natDegree_mul_le_of_le da (natDegree_X_pow_le k), ?_⟩
      simp only [eval, deg, value]
      rw [coeff_mul_X_pow, ca]

/-- The bit constraint `x·(x + 1)` of `qs_add_bit_constraint`, raised to degree `2 + k`. -/
def bitConstraint (j : ι) (k : ℕ) : QSExpr F ι :=
  raise k (mul (input j) (add (input j) (const 1 1)))

lemma bitConstraint_wf (j : ι) (k : ℕ) : (bitConstraint (F := F) j k).WF := by
  simp [bitConstraint, WF, deg]

lemma bitConstraint_deg (j : ι) (k : ℕ) : (bitConstraint (F := F) j k).deg = 2 + k := by
  simp [bitConstraint, deg]

lemma value_bitConstraint (w : ι → F) (j : ι) (k : ℕ) :
    value w (bitConstraint j k) = w j * (w j + 1) := by
  simp [bitConstraint, value]

end QSExpr

/-! ### The check polynomial -/

section Check

variable {F ι : Type*} [Field F]

/-- The verifier's check value as a polynomial in `Δ`: the ZKHash combination
`Σ_k χ_k p_k(Δ)` of the constraint MACs, plus `R(Δ)`, which collects the mask term, the prover's
`ã_1, …, ã_{d−1}` and the prover's check value. The proof is accepted at `Δ` only if this
vanishes. -/
noncomputable def checkPoly {n : ℕ} (q : ι → F[X]) (E : Fin n → QSExpr F ι) (χ : Fin n → F)
    (R : F[X]) : F[X] :=
  ∑ k, C (χ k) * (E k).eval q + R

/-- **The check polynomial has degree `≤ d`, and its `X^d` coefficient is `Σ_k χ_k f_k(w*)`.**
Hypotheses: each constraint is a well-formed circuit raised to degree `d` (`add_constraint`), the
witness MACs are affine with slopes `w*` (L3), and the remainder `R` has degree `≤ d − 1`. -/
theorem checkPoly_natDegree_coeff {n d : ℕ} (hd : 1 ≤ d) (q : ι → F[X]) (w : ι → F)
    (hq : ∀ j, (q j).natDegree ≤ 1 ∧ (q j).coeff 1 = w j) (E : Fin n → QSExpr F ι)
    (hE : ∀ k, (E k).WF ∧ (E k).deg = d) (χ : Fin n → F) (R : F[X]) (hR : R.natDegree ≤ d - 1) :
    (checkPoly q E χ R).natDegree ≤ d ∧
      (checkPoly q E χ R).coeff d = ∑ k, χ k * (E k).value w := by
  have hk : ∀ k, ((E k).eval q).natDegree ≤ d ∧ ((E k).eval q).coeff d = (E k).value w := by
    intro k
    have := QSExpr.eval_natDegree_coeff q w hq (E k) (hE k).1
    rwa [(hE k).2] at this
  refine ⟨?_, ?_⟩
  · refine (natDegree_add_le _ _).trans (max_le ?_ (hR.trans (Nat.sub_le d 1)))
    refine natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
    exact (natDegree_C_mul_le _ _).trans (hk k).1
  · have hR0 : R.coeff d = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    simp only [checkPoly, coeff_add, finsetSum_coeff, coeff_C_mul, hR0, add_zero]
    exact Finset.sum_congr rfl fun k _ => by rw [(hk k).2]

/-- The remainder as computed by the verifier (`quicksilver_state::verify` with `q_mask`): the
mask MACs `q_mask[i] = a_i + b_i·Δ` (L3) enter as `Σ_{i<d−1} q_mask[i]·Δ^i`, the prover's
`ã_i` as `Σ_{1≤i<d} ã_i Δ^i`, and the prover's check value `z` (an input to `H₂³`) as a
constant. -/
noncomputable def maskPoly (d : ℕ) (a b ã : ℕ → F) (z : F) : F[X] :=
  ∑ i ∈ range (d - 1), (C (a i) + C (b i) * X) * X ^ i + ∑ i ∈ Ico 1 d, C (ã i) * X ^ i + C z

/-- The masks and the prover's `ã_i` only reach degree `d − 1`, so they do not affect the top
coefficient. -/
theorem maskPoly_natDegree_le (d : ℕ) (a b ã : ℕ → F) (z : F) :
    (maskPoly d a b ã z).natDegree ≤ d - 1 := by
  unfold maskPoly
  refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
  · refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    have hi := Finset.mem_range.1 hi
    have h1 : (C (a i) + C (b i) * X).natDegree ≤ 1 :=
      (natDegree_add_le _ _).trans (max_le (by simp) (by simpa using natDegree_C_mul_X_pow_le (b i) 1))
    exact (natDegree_mul_le_of_le h1 (natDegree_X_pow_le i)).trans (by omega)
  · refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    have hi := Finset.mem_Ico.1 hi
    exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
  · simp

end Check

/-! ## 2. ZKHash as implemented, and its Schwartz–Zippel bound

`quicksilver_helpers::init_hashers` parses `chall₂` (56 bytes) as `r₀ ‖ r₁ ‖ s ‖ t`, with
`r₀, r₁, s ∈ F_{2^128}` and `t` a 64-bit polynomial, i.e. an element of the subset `S ⊆ F` of size
`2^64`. The two universal hashes are Horner evaluations (`uhasher_gfsecpar` in blocks of 8,
`uhasher_gfsecpar_64` one step at a time), and `finalize_hashes` combines them as
`r₀·H_s + r₁·H_t`. So the `k`-th of `n` constraints is weighted by
`χ_k = r₀ s^{n−1−k} + r₁ t^{n−1−k}`, as in the spec's ZKHash. -/

section ZKHash

variable {F : Type*} [Field F]

/-- One step of `uhasher_gfsecpar_64::update` per input: `state ← key·state + input`. -/
def horner (r : F) : (n : ℕ) → (Fin n → F) → F
  | 0, _ => 0
  | n + 1, x => r * horner r n (fun k => x k.castSucc) + x (Fin.last n)

/-- Horner's rule computes `Σ_k r^{n−1−k} x_k`. -/
theorem horner_eq_sum (r : F) : ∀ (n : ℕ) (x : Fin n → F),
    horner r n x = ∑ k : Fin n, r ^ (n - 1 - (k : ℕ)) * x k
  | 0, _ => by simp [horner]
  | n + 1, x => by
      rw [horner, horner_eq_sum r n, Fin.sum_univ_castSucc, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun k _ => ?_
        have hk := k.isLt
        simp only [Fin.val_castSucc]
        rw [← mul_assoc, ← pow_succ']
        congr 2
        omega
      · simp

/-- One step of `uhasher_gfsecpar::update` (with `PREP_KEY_POWS = 8`), on `(state, pow + 1)`. If
`pow = −1`, multiply the state by `key^8` and set `pow = 7`. Then add `key^pow · input`
(`key_pows[pow − 1] = key^pow`, and the input itself when `pow = 0`) and decrement `pow`. -/
def blockedStep (r : F) (sp : F × ℕ) (x : F) : F × ℕ :=
  let sp' := if sp.2 = 0 then (r ^ 8 * sp.1, 8) else sp
  (sp'.1 + r ^ (sp'.2 - 1) * x, sp'.2 - 1)

/-- `uhasher_gfsecpar` on the list of `n` inputs: `init(n)` sets `pow = (n + 7) mod 8`, which is
`(n − 1) mod 8` for `n ≥ 1`. Then `update` runs once per input. -/
def blockedHash (r : F) (xs : List F) : F :=
  (xs.foldl (blockedStep r) (0, (xs.length + 7) % 8 + 1)).1

/-- The invariant of the blocked Horner loop. -/
lemma blockedStep_foldl (r : F) : ∀ (xs : List F) (st : F) (p : ℕ), p ≤ xs.length →
    8 ∣ xs.length - p →
    (xs.foldl (blockedStep r) (st, p)).1 =
      r ^ (xs.length - p) * st + ∑ i : Fin xs.length, r ^ (xs.length - 1 - (i : ℕ)) * xs.get i
  | [], st, p, hp, _ => by simp at hp; simp [hp]
  | x :: xs, st, p, hp, hdvd => by
      simp only [List.length_cons] at hp hdvd ⊢
      rw [List.foldl_cons, Fin.sum_univ_succ]
      simp only [List.get_eq_getElem, Fin.val_zero, Fin.val_succ, List.getElem_cons_zero,
        List.getElem_cons_succ]
      have hsum : ∑ i : Fin xs.length, r ^ (xs.length + 1 - 1 - ((i : ℕ) + 1)) * xs[(i : ℕ)] =
          ∑ i : Fin xs.length, r ^ (xs.length - 1 - (i : ℕ)) * xs[(i : ℕ)] :=
        Finset.sum_congr rfl fun i _ => by congr 2; omega
      by_cases h0 : p = 0
      · subst h0
        have hL : 7 ≤ xs.length := by
          obtain ⟨c, hc⟩ := hdvd
          omega
        have hstep : blockedStep r (st, 0) x = (r ^ 8 * st + r ^ 7 * x, 7) := by
          simp [blockedStep]
        rw [hstep, blockedStep_foldl r xs _ 7 hL (by
          obtain ⟨c, hc⟩ := hdvd
          exact ⟨c - 1, by rw [Nat.mul_sub, mul_one]; omega⟩)]
        have e1 : xs.length - 7 + 8 = xs.length + 1 - 0 := by omega
        have e2 : xs.length - 7 + 7 = xs.length + 1 - 1 - 0 := by omega
        rw [← e1, ← e2, pow_add, pow_add, hsum]
        simp only [List.get_eq_getElem]
        ring
      · have hstep : blockedStep r (st, p) x = (st + r ^ (p - 1) * x, p - 1) := by
          simp [blockedStep, h0]
        rw [hstep, blockedStep_foldl r xs _ (p - 1) (by omega) (by
          have : xs.length - (p - 1) = xs.length + 1 - p := by omega
          rwa [this])]
        have e1 : xs.length - (p - 1) = xs.length + 1 - p := by omega
        have e2 : xs.length - (p - 1) + (p - 1) = xs.length + 1 - 1 - 0 := by omega
        rw [mul_add, ← mul_assoc, ← pow_add, e2, e1, hsum]
        simp only [List.get_eq_getElem]
        ring

/-- **`uhasher_gfsecpar` is Horner's rule.** When `update` is called exactly `n ≥ 1` times, as
`init(n)` requires (`FAEST_ASSERT(pow == -1)` in `finalize`), the blocked loop computes
`Σ_k r^{n−1−k} x_k`. -/
theorem blockedHash_eq_sum (r : F) (xs : List F) (hn : xs ≠ []) :
    blockedHash r xs = ∑ i : Fin xs.length, r ^ (xs.length - 1 - (i : ℕ)) * xs.get i := by
  have hlen : 0 < xs.length := List.length_pos_iff.2 hn
  have hp : (xs.length + 7) % 8 + 1 ≤ xs.length := by omega
  have hd : 8 ∣ xs.length - ((xs.length + 7) % 8 + 1) := by omega
  rw [blockedHash, blockedStep_foldl r xs 0 _ hp hd, mul_zero, zero_add]

/-- On the `n ≥ 1` constraint MACs in order, the blocked hash equals the plain Horner hash. -/
theorem blockedHash_ofFn (r : F) {n : ℕ} (hn : 0 < n) (f : Fin n → F) :
    blockedHash r (List.ofFn f) = horner r n f := by
  rw [blockedHash_eq_sum _ _ (by simp [List.ofFn_eq_nil_iff]; omega), horner_eq_sum]
  exact Fintype.sum_equiv (finCongr List.length_ofFn) _ _ fun i => by simp; left; rfl

/-- The ZKHash weight of constraint `k` of `n`. -/
def zkCoeff (n : ℕ) (r₀ r₁ s t : F) (k : Fin n) : F :=
  r₀ * s ^ (n - 1 - (k : ℕ)) + r₁ * t ^ (n - 1 - (k : ℕ))

/-- The ZKHash of the constraint vector `f` with `chall₂ = (r₀, r₁, s, t)`, as computed by the
code: `r₀·H_s(f) + r₁·H_t(f)`. -/
def zkHash (n : ℕ) (r₀ r₁ s t : F) (f : Fin n → F) : F :=
  r₀ * horner s n f + r₁ * horner t n f

lemma zkHash_eq_sum (n : ℕ) (r₀ r₁ s t : F) (f : Fin n → F) :
    zkHash n r₀ r₁ s t f = ∑ k, zkCoeff n r₀ r₁ s t k * f k := by
  simp only [zkHash, horner_eq_sum, zkCoeff, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- `zkHash` is what `finalize_hashes` computes from the two hashers: `r₀` times the blocked
`uhasher_gfsecpar` hash under `s`, plus `r₁` times the Horner `uhasher_gfsecpar_64` hash under
`t`. -/
lemma zkHash_eq_code {n : ℕ} (hn : 0 < n) (r₀ r₁ s t : F) (f : Fin n → F) :
    r₀ * blockedHash s (List.ofFn f) + r₁ * horner t n f = zkHash n r₀ r₁ s t f := by
  rw [blockedHash_ofFn s hn, zkHash]

/-- The polynomial `F_f(X) = Σ_k f_k X^{n−1−k}`. -/
noncomputable def zkPoly {n : ℕ} (f : Fin n → F) : F[X] :=
  ∑ k : Fin n, C (f k) * X ^ (n - 1 - (k : ℕ))

lemma eval_zkPoly {n : ℕ} (f : Fin n → F) (x : F) :
    (zkPoly f).eval x = ∑ k : Fin n, x ^ (n - 1 - (k : ℕ)) * f k := by
  simp only [zkPoly, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- `Σ_k χ_k f_k = r₀·F_f(s) + r₁·F_f(t)`. -/
lemma zkHash_eq_eval (n : ℕ) (r₀ r₁ s t : F) (f : Fin n → F) :
    zkHash n r₀ r₁ s t f = r₀ * (zkPoly f).eval s + r₁ * (zkPoly f).eval t := by
  simp only [zkHash, horner_eq_sum, eval_zkPoly]

lemma zkPoly_coeff {n : ℕ} (f : Fin n → F) (k : Fin n) :
    (zkPoly f).coeff (n - 1 - (k : ℕ)) = f k := by
  classical
  simp only [zkPoly, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    have : n - 1 - (k : ℕ) ≠ n - 1 - (j : ℕ) := by
      have := j.isLt; have := k.isLt
      intro h; exact hj (Fin.ext (by omega))
    simp [this]
  · simp

lemma zkPoly_ne_zero {n : ℕ} {f : Fin n → F} (hf : f ≠ 0) : zkPoly f ≠ 0 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hf
  intro h
  exact hk (by rw [← zkPoly_coeff f k, h, coeff_zero]; rfl)

lemma zkPoly_natDegree_le {n : ℕ} (f : Fin n → F) : (zkPoly f).natDegree ≤ n - 1 :=
  natDegree_sum_le_of_forall_le _ _ fun k _ => (natDegree_C_mul_X_pow_le _ _).trans (by omega)

variable [Fintype F] [DecidableEq F]

/-- The challenge space `F × F × F × S` of `(r₀, r₁, s, t)`. -/
def chalSpace (S : Finset F) : Finset (F × F × F × F) := univ ×ˢ (univ ×ˢ (univ ×ˢ S))

lemma card_chalSpace (S : Finset F) :
    #(chalSpace S) = Fintype.card F * (Fintype.card F * (Fintype.card F * #S)) := by
  simp [chalSpace, card_product]

/-- **Schwartz–Zippel for ZKHash, counting form.** For a nonzero `P` of degree `D`, the number of
`(r₀, r₁, s, t) ∈ F × F × F × S` with `r₀ P(s) + r₁ P(t) = 0` is at most
`|F|²·|S| + D²·|F|²`.

If `(P(s), P(t)) ≠ 0`, the pair `(r₀, r₁)` lies on a line, so `|F|` choices. Otherwise `s` and `t`
are both roots, at most `D` choices each. -/
theorem card_zk_bad_le {P : F[X]} (hP : P ≠ 0) (S : Finset F) :
    #{x ∈ chalSpace S | x.1 * P.eval x.2.2.1 + x.2.1 * P.eval x.2.2.2 = 0} ≤
      Fintype.card F * Fintype.card F * #S +
        P.natDegree * P.natDegree * (Fintype.card F * Fintype.card F) := by
  set q := Fintype.card F
  set Z := P.roots.toFinset
  have hZ : #Z ≤ P.natDegree := (Multiset.toFinset_card_le _).trans (card_roots' P)
  set A := {x ∈ chalSpace S | (P.eval x.2.2.1 ≠ 0 ∨ P.eval x.2.2.2 ≠ 0) ∧
    x.1 * P.eval x.2.2.1 + x.2.1 * P.eval x.2.2.2 = 0}
  set B : Finset (F × F × F × F) := univ ×ˢ (univ ×ˢ (Z ×ˢ Z))
  have hsub : {x ∈ chalSpace S | x.1 * P.eval x.2.2.1 + x.2.1 * P.eval x.2.2.2 = 0} ⊆ A ∪ B := by
    intro x hx
    obtain ⟨hxΩ, hx0⟩ := Finset.mem_filter.1 hx
    by_cases h : P.eval x.2.2.1 ≠ 0 ∨ P.eval x.2.2.2 ≠ 0
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hxΩ, h, hx0⟩)
    · push Not at h
      refine Finset.mem_union_right _ ?_
      simp only [B, Z, Finset.mem_product, Finset.mem_univ, true_and, Multiset.mem_toFinset,
        mem_roots hP, IsRoot.def]
      exact h
  -- `A` injects into `F × F × S` via `x ↦ (r₁ or r₀, s, t)`.
  have hA : #A ≤ q * q * #S := by
    let φ : F × F × F × F → F × F × F := fun x =>
      (if P.eval x.2.2.1 ≠ 0 then x.2.1 else x.1, x.2.2.1, x.2.2.2)
    have hmaps : ∀ x ∈ A, φ x ∈ (univ : Finset F) ×ˢ ((univ : Finset F) ×ˢ S) := by
      intro x hx
      obtain ⟨hxΩ, -⟩ := Finset.mem_filter.1 hx
      simp only [chalSpace, Finset.mem_product, Finset.mem_univ, true_and] at hxΩ
      simp [φ, hxΩ]
    have hinj : Set.InjOn φ A := by
      rintro ⟨a₀, a₁, s, t⟩ hx ⟨b₀, b₁, s', t'⟩ hy hφ
      obtain ⟨-, hx1, hx2⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hx)
      obtain ⟨-, -, hy2⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hy)
      simp only [φ, Prod.mk.injEq] at hφ hx1 hx2 hy2
      obtain ⟨h0, rfl, rfl⟩ := hφ
      by_cases hs : P.eval s ≠ 0
      · simp only [hs, ne_eq, not_false_eq_true, ite_true] at h0
        subst h0
        have : a₀ * P.eval s = b₀ * P.eval s := by linear_combination hx2 - hy2
        rw [mul_left_inj' hs] at this
        rw [this]
      · simp only [hs, ite_false] at h0
        subst h0
        have ht : P.eval t ≠ 0 := hx1.resolve_left hs
        push Not at hs
        rw [hs] at hx2 hy2
        have h1 : a₁ = 0 := by simpa [ht] using hx2
        have h2 : b₁ = 0 := by simpa [ht] using hy2
        rw [h1, h2]
    calc #A ≤ #((univ : Finset F) ×ˢ ((univ : Finset F) ×ˢ S)) :=
          Finset.card_le_card_of_injOn φ hmaps hinj
      _ = q * q * #S := by simp [card_product, q, mul_assoc]
  have hB : #B ≤ P.natDegree * P.natDegree * (q * q) := by
    simp only [B, card_product, card_univ]
    calc q * (q * (#Z * #Z)) = #Z * #Z * (q * q) := by ring
      _ ≤ P.natDegree * P.natDegree * (q * q) := by gcongr
  calc _ ≤ #(A ∪ B) := Finset.card_le_card hsub
    _ ≤ #A + #B := Finset.card_union_le _ _
    _ ≤ _ := add_le_add hA hB

/-- `ε_QS(n) = 1/|F| + (n − 1)²/(|F|·|S|)`. For `F = F_{2^128}` and `|S| = 2^64` this is
`2^{−128} + (n − 1)²·2^{−192}`. -/
noncomputable def epsQS (q s n : ℕ) : ℝ := 1 / q + ((n : ℝ) - 1) ^ 2 / (q * s)

/-- **Schwartz–Zippel for ZKHash, counting form for a constraint vector.** -/
theorem card_zkHash_eq_zero_le {n : ℕ} {f : Fin n → F} (hf : f ≠ 0) (S : Finset F) :
    #{x ∈ chalSpace S | zkHash n x.1 x.2.1 x.2.2.1 x.2.2.2 f = 0} ≤
      Fintype.card F * Fintype.card F * #S + (n - 1) * (n - 1) * (Fintype.card F * Fintype.card F) := by
  have h := card_zk_bad_le (zkPoly_ne_zero hf) S
  simp only [← zkHash_eq_eval] at h
  refine h.trans (Nat.add_le_add_left ?_ _)
  have := zkPoly_natDegree_le f
  gcongr

/-- **Schwartz–Zippel for ZKHash, probability form.** For a fixed nonzero constraint vector `f`
and a uniform challenge in `F × F × F × S`, `Pr[Σ_k χ_k f_k = 0] ≤ ε_QS(n)`. -/
theorem zkHash_prob_le {n : ℕ} {f : Fin n → F} (hf : f ≠ 0) (S : Finset F) (hS : S.Nonempty) :
    (#{x ∈ chalSpace S | zkHash n x.1 x.2.1 x.2.2.1 x.2.2.2 f = 0} : ℝ) / #(chalSpace S) ≤
      epsQS (Fintype.card F) #S n := by
  have h := card_zkHash_eq_zero_le hf S
  set q := Fintype.card F
  have hq : (0 : ℝ) < q := by exact_mod_cast Fintype.card_pos
  have hs : (0 : ℝ) < #S := by exact_mod_cast hS.card_pos
  rw [card_chalSpace, div_le_iff₀ (by positivity), epsQS]
  have h' : ((#{x ∈ chalSpace S | zkHash n x.1 x.2.1 x.2.2.1 x.2.2.2 f = 0} : ℕ) : ℝ) ≤
      (q : ℝ) * q * #S + ((n - 1 : ℕ) : ℝ) * ((n - 1 : ℕ) : ℝ) * (q * q) := by exact_mod_cast h
  have hn : ((n - 1 : ℕ) : ℝ) ^ 2 ≤ ((n : ℝ) - 1) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [Nat.cast_sub hn, Nat.cast_one]
  calc _ ≤ (q : ℝ) * q * #S + ((n - 1 : ℕ) : ℝ) ^ 2 * (q * q) := by rw [sq]; exact h'
    _ ≤ (q : ℝ) * q * #S + ((n : ℝ) - 1) ^ 2 * (q * q) := by gcongr
    _ = _ := by simp only [q]; push_cast; field_simp

end ZKHash

/-! ## 3. Challenge-dependent constraints

PomFRIT redeem, Moussaka redeem and Ratatouille spend have exactly one constraint slot `k₀` that
depends on `chall₂`, through `l = H(chall₂ ‖ dst) ∈ F^M`. Its value is linear in `l`:
`Σ_m l_m a_m(w*)`. The other slots `g_k(w*)` do not depend on `chall₂`. The *uncombined*
constraints are the `g_k` for `k ≠ k₀` together with the `M` components `a_m`.

In the random-oracle model, and conditioned on the prover's view before the `H₂²` answer (which
fixes `w*`, `g` and `a`), the pair `(chall₂, l)` is uniform on the product space except when the
point `chall₂ ‖ dst` was queried before. So it suffices to count over the product space, which is
what this section does. `χ` and `l` are both functions of `chall₂`. Counting over pairs is the
"joint distribution" argument: for each `l` the vector `f(l)` is fixed and Section 2 applies, and
the event `Σ_m l_m a_m = 0` is handled by `card_combination_eq_zero`. -/

section Combined

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The constraint vector with the combination `Σ_m l_m a_m` in slot `k₀`. -/
def combinedVec {n M : ℕ} (g : Fin n → F) (k₀ : Fin n) (a : Fin M → F) (l : Fin M → F) :
    Fin n → F :=
  Function.update g k₀ (∑ m, l m * a m)

/-- Some uncombined constraint fails. -/
def UncombinedFail {n M : ℕ} (g : Fin n → F) (k₀ : Fin n) (a : Fin M → F) : Prop :=
  (∃ k, k ≠ k₀ ∧ g k ≠ 0) ∨ a ≠ 0

/-- Counting a filter on a product by the right factor. -/
lemma card_filter_product_eq_sum {α β : Type*} (s : Finset α) (t : Finset β) (p : α × β → Prop)
    [DecidablePred p] :
    #{x ∈ s ×ˢ t | p x} = ∑ b ∈ t, #{a ∈ s | p (a, b)} := by
  rw [Finset.card_filter, Finset.sum_product_right]
  exact Finset.sum_congr rfl fun b _ => (Finset.card_filter _ _).symm

/-- **The composed bad event, counting form.** Over `(chall₂, l) ∈ (F × F × F × S) × F^M`: if
some uncombined constraint fails, the number of pairs with `Σ_k χ_k f_k(l) = 0` is at most
`|Ω|·|F|^{M−1} + |F|^M·B_QS`, where `B_QS = |F|²|S| + (n−1)²|F|²` bounds Section 2's count. -/
theorem card_combined_bad_le {n M : ℕ} (g : Fin n → F) (k₀ : Fin n) (a : Fin M → F)
    (hfail : UncombinedFail g k₀ a) (S : Finset F) :
    #{x ∈ chalSpace S ×ˢ (univ : Finset (Fin M → F)) |
        zkHash n x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2 (combinedVec g k₀ a x.2) = 0} * Fintype.card F ≤
      #(chalSpace S) * Fintype.card (Fin M → F) +
        Fintype.card (Fin M → F) *
          ((Fintype.card F * Fintype.card F * #S +
            (n - 1) * (n - 1) * (Fintype.card F * Fintype.card F)) * Fintype.card F) := by
  set Ω := chalSpace S
  set q := Fintype.card F
  set BQ := q * q * #S + (n - 1) * (n - 1) * (q * q)
  set Lz : Finset (Fin M → F) := {l | ∑ m, l m * a m = 0}
  -- The pairs where `f(l) ≠ 0` and the hash vanishes.
  set Y := {x ∈ Ω ×ˢ (univ : Finset (Fin M → F)) | combinedVec g k₀ a x.2 ≠ 0 ∧
    zkHash n x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2 (combinedVec g k₀ a x.2) = 0}
  have hY : #Y ≤ Fintype.card (Fin M → F) * BQ := by
    rw [card_filter_product_eq_sum]
    calc ∑ l ∈ (univ : Finset (Fin M → F)), #{c ∈ Ω | combinedVec g k₀ a l ≠ 0 ∧
            zkHash n c.1 c.2.1 c.2.2.1 c.2.2.2 (combinedVec g k₀ a l) = 0}
        ≤ ∑ _l ∈ (univ : Finset (Fin M → F)), BQ := by
          refine Finset.sum_le_sum fun l _ => ?_
          by_cases hl : combinedVec g k₀ a l = 0
          · simp [hl]
          · simp only [hl, ne_eq, not_false_eq_true, true_and]
            exact card_zkHash_eq_zero_le hl S
      _ = _ := by simp
  -- If some fixed slot fails, `f(l) ≠ 0` for every `l`; otherwise `a ≠ 0`, and `f(l) ≠ 0` unless
  -- `Σ_m l_m a_m = 0`.
  have hsub : {x ∈ Ω ×ˢ (univ : Finset (Fin M → F)) |
      zkHash n x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2 (combinedVec g k₀ a x.2) = 0} ⊆
      (if a ≠ 0 then Ω ×ˢ Lz else ∅) ∪ Y := by
    intro x hx
    obtain ⟨hxΩ, hx0⟩ := Finset.mem_filter.1 hx
    by_cases hf : combinedVec g k₀ a x.2 = 0
    · refine Finset.mem_union_left _ ?_
      have hk₀ : ∑ m, x.2 m * a m = 0 := by
        have := congrFun hf k₀
        simpa [combinedVec] using this
      have ha : a ≠ 0 := by
        rcases hfail with ⟨k, hk, hg⟩ | ha
        · exact absurd (by simpa [combinedVec, hk] using congrFun hf k) hg
        · exact ha
      simp only [ha, ne_eq, not_false_eq_true, ite_true]
      exact Finset.mem_product.2 ⟨(Finset.mem_product.1 hxΩ).1, by simp [Lz, hk₀]⟩
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hxΩ, hf, hx0⟩)
  have hX : #(if a ≠ 0 then Ω ×ˢ Lz else ∅) * q ≤ #Ω * Fintype.card (Fin M → F) := by
    by_cases ha : a = 0
    · simp [ha]
    · simp only [ne_eq, ha, not_false_eq_true, ite_true, card_product, mul_assoc]
      rw [VoleMole.SeedExtraction.card_combination_eq_zero a ha]
  calc _ ≤ #((if a ≠ 0 then Ω ×ˢ Lz else ∅) ∪ Y) * q := Nat.mul_le_mul_right _ (card_le_card hsub)
    _ ≤ (#(if a ≠ 0 then Ω ×ˢ Lz else ∅) + #Y) * q := Nat.mul_le_mul_right _ (card_union_le _ _)
    _ = #(if a ≠ 0 then Ω ×ˢ Lz else ∅) * q + #Y * q := add_mul _ _ _
    _ ≤ _ := by
        rw [← mul_assoc]
        exact add_le_add hX (Nat.mul_le_mul_right _ hY)

/-- **Lemma L4's probability bound (product-space form).** If some uncombined constraint fails at
`w*`, then over a uniform `chall₂ = (r₀, r₁, s, t) ∈ F × F × F × S` and an independent uniform
`l ∈ F^M`, the QuickSilver top coefficient `Σ_k χ_k f_k(w*; l)` vanishes with probability at most
`ε_QS(n) + 1/|F|`. -/
theorem combined_prob_le {n M : ℕ} (g : Fin n → F) (k₀ : Fin n) (a : Fin M → F)
    (hfail : UncombinedFail g k₀ a) (S : Finset F) (hS : S.Nonempty) :
    (#{x ∈ chalSpace S ×ˢ (univ : Finset (Fin M → F)) |
        zkHash n x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2 (combinedVec g k₀ a x.2) = 0} : ℝ) /
        (#(chalSpace S) * Fintype.card (Fin M → F)) ≤
      epsQS (Fintype.card F) #S n + 1 / Fintype.card F := by
  have h := card_combined_bad_le g k₀ a hfail S
  set N := #{x ∈ chalSpace S ×ˢ (univ : Finset (Fin M → F)) |
        zkHash n x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2 (combinedVec g k₀ a x.2) = 0}
  set q := Fintype.card F
  set L := Fintype.card (Fin M → F)
  have hq : (0 : ℝ) < q := by exact_mod_cast Fintype.card_pos
  have hL : (0 : ℝ) < L := by exact_mod_cast Fintype.card_pos
  have hs : (0 : ℝ) < #S := by exact_mod_cast hS.card_pos
  have hΩ : (#(chalSpace S) : ℝ) = q * (q * (q * #S)) := by
    rw [card_chalSpace]; push_cast; rfl
  have h' : (N : ℝ) * q ≤ #(chalSpace S) * L +
      L * ((q * q * #S + ((n - 1 : ℕ) : ℝ) * ((n - 1 : ℕ) : ℝ) * (q * q)) * q) := by
    exact_mod_cast h
  have hn : ((n - 1 : ℕ) : ℝ) ^ 2 ≤ ((n : ℝ) - 1) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [Nat.cast_sub hn, Nat.cast_one]
  rw [hΩ] at h' ⊢
  rw [div_le_iff₀ (by positivity), epsQS]
  have key : (N : ℝ) * q ≤ q * (q * (q * #S)) * L +
      L * ((q * q * #S + ((n : ℝ) - 1) ^ 2 * (q * q)) * q) := by
    refine h'.trans ?_
    gcongr
    rw [← sq]; exact hn
  have : (N : ℝ) ≤ (q * (q * (q * #S)) * L +
      L * ((q * q * #S + ((n : ℝ) - 1) ^ 2 * (q * q)) * q)) / q := by
    rw [le_div_iff₀ hq]; exact key
  refine this.trans (le_of_eq ?_)
  field_simp
  ring

end Combined

/-! ## 4. Glue: Claim 3 in the form consumed by `extraction_cases` -/

section Glue

open VoleMole.SeedExtraction

variable {ι J F : Type*} [Fintype ι] [DecidableEq ι] [Field F]
variable {B : ι → Type*} [∀ i, AddCommGroup (B i)]

/-- **Claim 3 on a good challenge.** Let `p` be the chain's check polynomial, of degree `≤ d`,
vanishing at `e(Δ')` for every `Δ' ∈ A`. Suppose its `X^d` coefficient `T` is nonzero unless `sat`
holds (where `sat` says every uncombined constraint holds). This is the good-`chall₂` event of
Section 3. Then `sat ∨ |A| ≤ d`, which is `hclaim3` of `extraction_cases`. -/
theorem claim3_of_good [DecidableEq F] {e : (∀ i, B i) →+ F} (he : Function.Injective e)
    {A : Finset (∀ i, B i)} {p : F[X]} {d : ℕ} (hdeg : p.natDegree ≤ d) {T : F}
    (htop : p.coeff d = T) (hroot : ∀ Δ ∈ A, p.eval (e Δ) = 0) {sat : Prop}
    (hgood : ¬sat → T ≠ 0) : sat ∨ A.card ≤ d := by
  by_cases hs : sat
  · exact Or.inl hs
  · refine Or.inr ?_
    have hp : p ≠ 0 := by
      intro h
      exact hgood hs (by rw [← htop, h, coeff_zero])
    exact (card_le_natDegree he hp hroot).trans hdeg

/-- **Claim 3, per chain, from the circuit model.** The check polynomial of Section 1 with
constraint circuits `E` of degree `d`, affine witness MACs with slopes `w*`, and a remainder of
degree `≤ d − 1`. If the top coefficient `Σ_k χ_k f_k(w*)` is nonzero whenever some uncombined
constraint fails, then every uncombined constraint holds or `|A| ≤ d`. -/
theorem claim3_of_circuit [DecidableEq F] {n d : ℕ} (hd : 1 ≤ d) {e : (∀ i, B i) →+ F}
    (he : Function.Injective e) {A : Finset (∀ i, B i)} (q : J → F[X]) (w : J → F)
    (hq : ∀ j, (q j).natDegree ≤ 1 ∧ (q j).coeff 1 = w j) (E : Fin n → QSExpr F J)
    (hE : ∀ k, (E k).WF ∧ (E k).deg = d) (χ : Fin n → F) (R : F[X]) (hR : R.natDegree ≤ d - 1)
    (hroot : ∀ Δ ∈ A, (checkPoly q E χ R).eval (e Δ) = 0) {sat : Prop}
    (hgood : ¬sat → ∑ k, χ k * (E k).value w ≠ 0) : sat ∨ A.card ≤ d := by
  obtain ⟨hdeg, htop⟩ := checkPoly_natDegree_coeff hd q w hq E hE χ R hR
  exact claim3_of_good he hdeg htop hroot hgood

/-- **The bit constraints give `hbits`.** In characteristic 2, if every `w*_j` satisfies the bit
constraint `w*_j (w*_j + 1) = 0`, and `w* = u* + d` with `d` a bit vector, then `u*` is a bit
vector. (In odd characteristic `u*_j = w*_j − d_j` could be `−1`.) -/
theorem bits_of_bit_constraints [CharP F 2] (w uStar d : J → F)
    (hw : ∀ j, w j * (w j + 1) = 0) (hd : ∀ j, d j = 0 ∨ d j = 1) (hwud : w = uStar + d) :
    ∀ j, uStar j = 0 ∨ uStar j = 1 := by
  intro j
  have hu : uStar j = w j + d j := by
    have := congrFun hwud j
    simp only [Pi.add_apply] at this
    rw [this, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hwj : w j = 0 ∨ w j = 1 := by
    rcases mul_eq_zero.1 (hw j) with h | h
    · exact Or.inl h
    · right
      have := CharTwo.add_self_eq_zero (1 : F)
      linear_combination h - this
  rcases hwj with h1 | h1 <;> rcases hd j with h2 | h2 <;> simp [hu, h1, h2, CharTwo.add_self_eq_zero]

end Glue

end VoleMole.Seed
