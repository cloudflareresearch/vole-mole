import Mathlib.FieldTheory.Finite.Extension
import VoleMole.Arith.GF

/-!
# `GF128` is the field GF(2¹²⁸) (kernel-checked)

`Arith/GF.lean` defines `GF128` (two `UInt64`s, polynomials over GF(2) of degree `< 128`, multiplied
modulo `X¹²⁸ + X⁷ + X² + X + 1`) with only `0`, `1`, `+`, `*`. This file proves that these make it
the field with `2¹²⁸` elements, without `native_decide`:

* **Evaluation.** For any commutative ring `R` of characteristic 2 and `r : R` with
  `r¹²⁸ = r⁷ + r² + r + 1` (`IsModRoot`), `eval r a = Σ_i a_i rⁱ` preserves `1`, `+` and `*`
  (`eval_one`, `eval_add`, `eval_mul`). Symbolic proof: `eval (mulX a) = r · eval a` from the bit
  formulas of the shifts, then induction along `mulWord`.
* **Irreducibility** (`irreducible_modulus`). Mathlib's
  `Irreducible.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X` (an irreducible `f` over GF(q) divides
  `X^(q^n) − X` iff `deg f ∣ n`) reduces it to `modulus ∣ X^(2¹²⁸) − X` and
  `IsCoprime modulus (X^(2⁶⁴) − X)`: then every irreducible factor has degree dividing 128 but not
  64, i.e. degree 128. Both are computed in `GF128` by the kernel (`decide +kernel`, ≈ 200 products)
  and carried to `GF(2)[X]/(modulus)` by `eval` at the root: `X^(2¹²⁸) = X` (`sqIter_128`, 128
  squarings of `X`), and `(X^(2⁶⁴) + X) · bezout = 1` for an inverse `bezout` computed offline
  (`sqIter_64_bezout`).
* **The field.** `K = AdjoinRoot modulus` is then a field with `card_K : Fintype.card K = 2¹²⁸`
  (power basis), `eval (root)` is injective (a nonzero polynomial of degree `< 128` is not divisible
  by the modulus), hence bijective by counting (`eval_bijective`). `ringEquivK : GF128 ≃+* K`, and
  `instField : Field GF128` keeps `GF.lean`'s `0`, `1`, `+`, `*` and transports the rest from `K`.

`Verifier/Bridge/Concrete.lean` uses this to discharge the field-embedding hypothesis of the
verifier bridge theorems.
-/

namespace VoleMole.Arith

namespace GF128

/-! ## Evaluation at a root of the modulus -/

section Eval

variable {R : Type*} [CommRing R] (r : R)

/-- `1` if the bit is set, else `0`. -/
def bitR (b : Bool) : R := if b then 1 else 0

/-- `Σ_{i<n} w_i rⁱ`. -/
def wordSum (n : ℕ) (w : UInt64) : R :=
  ∑ i ∈ Finset.range n, bitR (w.toBitVec.getLsbD i) * r ^ i

/-- The value at `X = r` of the polynomial `a`: `Σ_{i<64} lo_i rⁱ + r⁶⁴ Σ_{i<64} hi_i rⁱ`. -/
def eval (a : GF128) : R := wordSum r 64 a.lo + r ^ 64 * wordSum r 64 a.hi

lemma getLsbD_shr1 (w : UInt64) (i : ℕ) :
    (w >>> 1).toBitVec.getLsbD i = w.toBitVec.getLsbD (i + 1) := by
  simp [UInt64.toBitVec_shiftRight, BitVec.getLsbD_ushiftRight, Nat.add_comm]

lemma getLsbD_shl1 (w : UInt64) (i : ℕ) :
    (w <<< 1).toBitVec.getLsbD (i + 1) = (decide (i + 1 < 64) && w.toBitVec.getLsbD i) := by
  simp [UInt64.toBitVec_shiftLeft, BitVec.getLsbD_shiftLeft]

lemma shr63 (w : UInt64) : w >>> 63 = if w.toBitVec.getLsbD 63 then 1 else 0 := by
  apply UInt64.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · split <;> simp_all [UInt64.toBitVec_shiftRight]
  · have : 64 ≤ 63 + i := by omega
    split <;> simp_all [UInt64.toBitVec_shiftRight, BitVec.getLsbD_of_ge, Nat.pos_iff_ne_zero]

variable {r}

lemma bitR_xor (h2 : (2 : R) = 0) (x y : Bool) : bitR (x ^^ y) = (bitR x + bitR y : R) := by
  cases x <;> cases y <;> simp [bitR, one_add_one_eq_two, h2]

lemma wordSum_xor (h2 : (2 : R) = 0) (n : ℕ) (w1 w2 : UInt64) :
    wordSum r n (w1 ^^^ w2) = wordSum r n w1 + wordSum r n w2 := by
  simp only [wordSum, UInt64.toBitVec_xor, BitVec.getLsbD_xor, bitR_xor h2, _root_.add_mul,
    Finset.sum_add_distrib]

lemma wordSum_shr1 (n : ℕ) (w : UInt64) :
    wordSum r (n + 1) w = bitR (w.toBitVec.getLsbD 0) + r * wordSum r n (w >>> 1) := by
  simp only [wordSum, Finset.sum_range_succ', getLsbD_shr1, Finset.mul_sum, pow_zero, mul_one,
    pow_succ]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

lemma wordSum_shl1 (w : UInt64) :
    wordSum r 64 (w <<< 1) + bitR (w.toBitVec.getLsbD 63) * r ^ 64 = r * wordSum r 64 w := by
  have e1 : wordSum r 64 (w <<< 1) =
      ∑ i ∈ Finset.range 63, bitR ((w <<< 1).toBitVec.getLsbD (i + 1)) * r ^ (i + 1) +
        bitR ((w <<< 1).toBitVec.getLsbD 0) * r ^ 0 := Finset.sum_range_succ' _ _
  have e2 : wordSum r 64 w = ∑ i ∈ Finset.range 63, bitR (w.toBitVec.getLsbD i) * r ^ i +
      bitR (w.toBitVec.getLsbD 63) * r ^ 63 := Finset.sum_range_succ _ _
  have h0 : (w <<< 1).toBitVec.getLsbD 0 = false := by simp [UInt64.toBitVec_shiftLeft]
  have hs : ∑ i ∈ Finset.range 63, bitR ((w <<< 1).toBitVec.getLsbD (i + 1)) * r ^ (i + 1) =
      ∑ i ∈ Finset.range 63, r * (bitR (w.toBitVec.getLsbD i) * r ^ i) :=
    Finset.sum_congr rfl fun i hi => by
      rw [getLsbD_shl1, show decide (i + 1 < 64) = true by simp at hi; simp; omega,
        Bool.true_and, pow_succ]; ring
  rw [e1, e2, h0, hs, _root_.mul_add, Finset.mul_sum]
  simp only [bitR, Bool.false_eq_true, ↓reduceIte]
  ring

/-- `wordSum` of a word with the single bit `k`. -/
lemma wordSum_single (w : UInt64) (k : ℕ) (hk : k < 64)
    (hw : ∀ i : Fin 64, w.toBitVec.getLsbD i = decide (i.val = k)) : wordSum r 64 w = r ^ k := by
  rw [wordSum, Finset.sum_eq_single k]
  · simp [hw ⟨k, hk⟩, bitR]
  · intro i hi hik
    simp [hw ⟨i, Finset.mem_range.1 hi⟩, bitR, hik]
  · simp [hk]

lemma wordSum_zero : wordSum r 64 0 = 0 := by simp [wordSum, bitR]

lemma wordSum_bit (b : Bool) : wordSum r 64 (if b then 1 else 0) = bitR b := by
  cases b
  · simp [wordSum_zero, bitR]
  · simpa [bitR] using wordSum_single (r := r) 1 0 (by omega) (by decide)

/-- `X¹²⁸ = X⁷ + X² + X + 1`, in characteristic 2. -/
structure IsModRoot (r : R) : Prop where
  two : (2 : R) = 0
  pow128 : r ^ 128 = r ^ 7 + r ^ 2 + r + 1

variable (hr : IsModRoot r)
include hr

lemma IsModRoot.add_self (x : R) : x + x = 0 := by
  linear_combination x * hr.two

lemma eval_add (a b : GF128) : eval r (a + b) = eval r a + eval r b := by
  simp only [eval, add_lo, add_hi, wordSum_xor hr.two]; ring

lemma eval_mulX (a : GF128) : eval r (mulX a) = r * eval r a := by
  have h1 := wordSum_shl1 (r := r) a.lo
  have h2 := wordSum_shl1 (r := r) a.hi
  simp only [eval, mulX, shr63]
  cases hb : a.hi.toBitVec.getLsbD 63 <;>
    simp only [hb, bitR, Bool.false_eq_true, ↓reduceIte] at h2 ⊢
  · simp only [show ((0 : UInt64) <<< 1) = 0 from rfl, show ((0 : UInt64) <<< 2) = 0 from rfl,
      show ((0 : UInt64) <<< 7) = 0 from rfl, UInt64.xor_zero, wordSum_xor hr.two, wordSum_bit]
    linear_combination (r ^ 64) * h2 + h1
  · simp only [show ((1 : UInt64) <<< 1) = 2 from rfl, show ((1 : UInt64) <<< 2) = 4 from rfl,
      show ((1 : UInt64) <<< 7) = 128 from rfl, wordSum_xor hr.two, wordSum_bit]
    rw [wordSum_single 1 0 (by omega) (by decide), wordSum_single 2 1 (by omega) (by decide),
      wordSum_single 4 2 (by omega) (by decide), wordSum_single 128 7 (by omega) (by decide)]
    linear_combination (r ^ 64) * h2 + h1 - hr.pow128

lemma eval_mulWord (n : ℕ) (w : UInt64) (acc p : GF128) :
    eval r (mulWord n w acc p).1 = eval r acc + wordSum r n w * eval r p := by
  induction n generalizing w acc p with
  | zero => simp [mulWord, wordSum]
  | succ n ih =>
    rw [mulWord, ih, eval_mulX hr, wordSum_shr1]
    cases w.toBitVec.getLsbD 0 <;> simp only [bitR, Bool.false_eq_true, ↓reduceIte] <;>
      [ring; (rw [eval_add hr]; ring)]

lemma eval_xpow (n : ℕ) (p : GF128) : eval r (xpow n p) = r ^ n * eval r p := by
  induction n generalizing p with
  | zero => simp [xpow]
  | succ n ih => rw [xpow, ih, eval_mulX hr]; ring

lemma eval_mul (a b : GF128) : eval r (a * b) = eval r a * eval r b := by
  show eval r (mulWord 64 a.hi _ _).1 = _
  rw [eval_mulWord hr, eval_mulWord hr, mulWord_snd_eq, eval_xpow hr]
  simp only [eval, show (0 : GF128) = ⟨0, 0⟩ from rfl, wordSum_zero]
  ring

omit hr in
lemma eval_one : eval r 1 = 1 := by
  simp only [eval, show (1 : GF128) = ⟨1, 0⟩ from rfl, wordSum_zero,
    wordSum_single 1 0 (by omega) (by decide)]
  ring

omit hr in
/-- `X` evaluates to `r`. -/
lemma eval_X : eval r ⟨2, 0⟩ = r := by
  simp only [eval, wordSum_zero, wordSum_single 2 1 (by omega) (by decide)]
  ring

end Eval


/-! ## The modulus is irreducible -/

open Polynomial

/-- `X¹²⁸ + X⁷ + X² + X + 1` over GF(2). -/
noncomputable def modulus : (ZMod 2)[X] := X ^ 128 + X ^ 7 + X ^ 2 + X + 1

lemma modulus_eq : modulus = X ^ 128 + X ^ 7 + X ^ 2 + X + 1 := by unfold modulus; exact Eq.refl _

-- Unfolding `modulus` makes the unifier expand `X ^ 128` (and hit the recursion limit), so it is
-- only ever rewritten with `modulus_eq`.
attribute [irreducible] modulus

lemma modulus_monic : modulus.Monic := by rw [modulus_eq]; monicity!

lemma modulus_natDegree : modulus.natDegree = 128 := by rw [modulus_eq]; compute_degree!

/-- The root of the modulus in `GF(2)[X]/(modulus)` (a commutative ring; a field once the modulus is
irreducible). -/
lemma isRoot_root : IsModRoot (AdjoinRoot.root modulus) := by
  have two : (2 : AdjoinRoot modulus) = 0 := calc
    (2 : AdjoinRoot modulus) = AdjoinRoot.of modulus 2 := (map_ofNat _ 2).symm
    _ = AdjoinRoot.of modulus 0 := congrArg _ (by decide)
    _ = 0 := map_zero _
  have h := AdjoinRoot.mk_self (f := modulus)
  conv at h => lhs; arg 2; rw [modulus_eq]
  simp only [map_add, map_pow, AdjoinRoot.mk_X, map_one] at h
  exact ⟨two, by linear_combination h - (AdjoinRoot.root modulus ^ 7 + AdjoinRoot.root modulus ^ 2 +
    AdjoinRoot.root modulus + 1) * two⟩

/-- `a^(2^n)`, by `n` squarings. -/
def sqIter : ℕ → GF128 → GF128
  | 0, a => a
  | n + 1, a => sqIter n (a * a)

/-- `X^(2¹²⁸) = X` (kernel computation: 128 squarings). -/
theorem sqIter_128 : sqIter 128 ⟨2, 0⟩ = ⟨2, 0⟩ := by decide +kernel

/-- `X^(2⁶⁴) + X` is invertible, with inverse `bezout` (computed offline, checked by the kernel). -/
def bezout : GF128 := ⟨0x41a8cafd2c95b018, 0x9e4af928ddbc838a⟩

theorem sqIter_64_bezout : (sqIter 64 ⟨2, 0⟩ + ⟨2, 0⟩) * bezout = 1 := by decide +kernel

section Eval
variable {R : Type*} [CommRing R] {r : R} (hr : IsModRoot r)
include hr

lemma eval_sqIter (n : ℕ) (a : GF128) : eval r (sqIter n a) = eval r a ^ 2 ^ n := by
  induction n generalizing a with
  | zero => simp [sqIter]
  | succ n ih => rw [sqIter, ih, eval_mul hr, ← sq, ← pow_mul, pow_succ']

end Eval

-- The exponents `2^n` stay symbolic: the kernel must not see `2¹²⁸` inside a `rw` motive.
lemma modulus_dvd_of {n : ℕ} (h : sqIter n ⟨2, 0⟩ = ⟨2, 0⟩) : modulus ∣ X ^ 2 ^ n - X := by
  rw [← AdjoinRoot.mk_eq_zero]
  have := congrArg (eval (AdjoinRoot.root modulus)) h
  rw [eval_sqIter isRoot_root, eval_X] at this
  rw [map_sub, map_pow, AdjoinRoot.mk_X, this, sub_self]

lemma modulus_coprime_of {n : ℕ} {u : GF128} (h : (sqIter n ⟨2, 0⟩ + ⟨2, 0⟩) * u = 1) :
    IsCoprime modulus (X ^ 2 ^ n - X) := by
  have h := congrArg (eval (AdjoinRoot.root modulus)) h
  rw [eval_mul isRoot_root, eval_add isRoot_root, eval_sqIter isRoot_root, eval_X,
    eval_one] at h
  obtain ⟨v, hv⟩ := AdjoinRoot.mk_surjective (eval (AdjoinRoot.root modulus) u)
  obtain ⟨w, hw⟩ : modulus ∣ (X ^ 2 ^ n - X) * v - 1 := by
    rw [← AdjoinRoot.mk_eq_zero]
    simp only [map_sub, map_mul, map_pow, AdjoinRoot.mk_X, map_one, hv]
    linear_combination h - AdjoinRoot.root modulus * eval (AdjoinRoot.root modulus) u *
      isRoot_root.two
  exact ⟨-w, v, by linear_combination hw⟩

lemma modulus_dvd_128 : modulus ∣ X ^ 2 ^ 128 - X := modulus_dvd_of sqIter_128

lemma modulus_coprime_64 : IsCoprime modulus (X ^ 2 ^ 64 - X) :=
  modulus_coprime_of sqIter_64_bezout

/-- **`X¹²⁸ + X⁷ + X² + X + 1` is irreducible over GF(2)**: every irreducible factor `f` divides
`X^(2¹²⁸) − X`, so its degree divides 128, and does not divide `X^(2⁶⁴) − X`, so its degree does
not divide 64; hence it has degree 128. -/
theorem irreducible_modulus : Irreducible modulus := by
  have hcard : Nat.card (ZMod 2) = 2 := by simp
  have hdeg : ∀ f, Irreducible f → f ∣ modulus → f.natDegree = 128 := by
    intro f hf hfp
    have h1 : f.natDegree ∣ 128 :=
      hf.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X (by rw [hcard]; exact hfp.trans modulus_dvd_128)
    have h2 : ¬ f.natDegree ∣ 64 := fun h =>
      hf.not_isUnit (modulus_coprime_64.isUnit_of_dvd' hfp
        (by simpa [hcard] using (hf.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X (n := 64)).1 h))
    obtain ⟨m, hm, he⟩ := (Nat.dvd_prime_pow (p := 2) Nat.prime_two).1 (show f.natDegree ∣ 2 ^ 7 from h1)
    rw [he] at h2 ⊢
    interval_cases m <;> simp_all
  have h0 : modulus ≠ 0 := modulus_monic.ne_zero
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · have := natDegree_eq_zero_of_isUnit hu
    rw [modulus_natDegree] at this
    exact absurd this (by norm_num)
  by_contra hn
  obtain ⟨ha, hb⟩ := not_or.1 hn
  have ha0 : a ≠ 0 := by rintro rfl; exact h0 (by simpa using hab)
  have hb0 : b ≠ 0 := by rintro rfl; exact h0 (by simpa using hab)
  obtain ⟨f, hf, hfa⟩ := WfDvdMonoid.exists_irreducible_factor ha ha0
  have hfd := hdeg f hf (hfa.trans (hab ▸ dvd_mul_right a b))
  have hda := natDegree_le_of_dvd hfa ha0
  have hsum : modulus.natDegree = a.natDegree + b.natDegree := hab ▸ natDegree_mul ha0 hb0
  rw [modulus_natDegree] at hsum
  have hb' : b.natDegree = 0 := by omega
  exact hb (isUnit_iff_degree_eq_zero.2 (by rw [degree_eq_natDegree hb0, hb']; rfl))

/-! ## The field `K = GF(2)[X]/(X¹²⁸ + X⁷ + X² + X + 1)` and the isomorphism -/

instance : Fact (Irreducible modulus) := ⟨irreducible_modulus⟩

/-- GF(2¹²⁸) in Mathlib: `GF(2)[X]/(X¹²⁸ + X⁷ + X² + X + 1)`, a field by `irreducible_modulus`. -/
abbrev K := AdjoinRoot modulus

instance : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

noncomputable instance : Fintype K :=
  Fintype.ofEquiv _ (AdjoinRoot.powerBasis' modulus_monic).basis.equivFun.toEquiv.symm

theorem card_K : Fintype.card K = 2 ^ 128 := by
  rw [Module.card_fintype (AdjoinRoot.powerBasis' modulus_monic).basis]
  simp [modulus_natDegree]

/-- `Σ_{i<n} w_i Xⁱ`. -/
noncomputable def wordPoly (n : ℕ) (w : UInt64) : (ZMod 2)[X] :=
  ∑ i ∈ Finset.range n, C (bitR (w.toBitVec.getLsbD i)) * X ^ i

/-- The polynomial of degree `< 128` that `a` stands for. -/
noncomputable def toPoly (a : GF128) : (ZMod 2)[X] := wordPoly 64 a.lo + X ^ 64 * wordPoly 64 a.hi

lemma mk_toPoly (a : GF128) :
    AdjoinRoot.mk modulus (toPoly a) = eval (AdjoinRoot.root modulus) a := by
  have hb : ∀ b : Bool, AdjoinRoot.mk modulus (C (bitR b)) = bitR b := by
    intro b; cases b <;> simp [bitR]
  simp only [toPoly, wordPoly, eval, wordSum, map_add, map_mul, map_sum, map_pow, AdjoinRoot.mk_X,
    hb]

lemma coeff_wordPoly (n : ℕ) (w : UInt64) (m : ℕ) :
    (wordPoly n w).coeff m = if m < n then bitR (w.toBitVec.getLsbD m) else 0 := by
  simp [wordPoly, coeff_C_mul, coeff_X_pow]

lemma coeff_toPoly (a : GF128) (m : ℕ) : (toPoly a).coeff m =
    (if m < 64 then bitR (a.lo.toBitVec.getLsbD m) else 0) +
      if 64 ≤ m then (if m - 64 < 64 then bitR (a.hi.toBitVec.getLsbD (m - 64)) else 0) else 0 := by
  rw [toPoly, coeff_add, mul_comm, coeff_mul_X_pow', coeff_wordPoly, coeff_wordPoly]

lemma bitR_eq_zero {b : Bool} (h : (bitR b : ZMod 2) = 0) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

lemma degree_toPoly (a : GF128) : (toPoly a).degree < modulus.degree := by
  rw [degree_eq_natDegree modulus_monic.ne_zero, modulus_natDegree, degree_lt_iff_coeff_zero]
  intro m hm
  have : 128 ≤ m := by exact_mod_cast hm
  rw [coeff_toPoly, ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_right (by omega), add_zero]

lemma eval_eq_zero {a : GF128} (h : eval (AdjoinRoot.root modulus) a = 0) : a = 0 := by
  rw [← mk_toPoly, AdjoinRoot.mk_eq_zero] at h
  have hq := eq_zero_of_dvd_of_degree_lt h (degree_toPoly a)
  have hc : ∀ m, (toPoly a).coeff m = 0 := fun m => by rw [hq, coeff_zero]
  have hc : ∀ m, (toPoly a).coeff m = 0 := fun m => by rw [hq, coeff_zero]
  have hlo : a.lo = 0 := by
    apply UInt64.toBitVec_inj.1
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := hc i
    rw [coeff_toPoly, ite_eq_left hi, ite_eq_right (by omega), add_zero] at this
    rw [bitR_eq_zero this]
    simp
  have hhi : a.hi = 0 := by
    apply UInt64.toBitVec_inj.1
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := hc (64 + i)
    rw [coeff_toPoly, ite_eq_right (by omega), ite_eq_left (by omega), show 64 + i - 64 = i by omega,
      ite_eq_left hi, zero_add] at this
    rw [bitR_eq_zero this]
    simp
  exact ext' hlo hhi

theorem eval_injective : Function.Injective (eval (AdjoinRoot.root modulus)) := by
  intro a b h
  have h0 : a + b = 0 := eval_eq_zero (by rw [eval_add isRoot_root, h]; exact isRoot_root.add_self _)
  calc a = a + (b + b) := by rw [XorGroup.add_self, XorGroup.add_zero]
    _ = b := by rw [← XorGroup.add_assoc, h0, XorGroup.zero_add]

/-- `GF128` as a pair of 64-bit words. -/
def equivWords : GF128 ≃ Fin (2 ^ 64) × Fin (2 ^ 64) where
  toFun a := (a.lo.toFin, a.hi.toFin)
  invFun p := ⟨UInt64.ofFin p.1, UInt64.ofFin p.2⟩
  left_inv a := by simp
  right_inv p := by simp

instance : Fintype GF128 := Fintype.ofEquiv _ equivWords.symm

theorem card_eq : Fintype.card GF128 = 2 ^ 128 := by
  rw [Fintype.card_congr equivWords]; simp

theorem eval_bijective : Function.Bijective (eval (AdjoinRoot.root modulus)) :=
  (Fintype.bijective_iff_injective_and_card _).2 ⟨eval_injective, by rw [card_eq, card_K]⟩

/-- `a ↦ a(root)`, a bijection `GF128 ≃ K` preserving `0`, `1`, `+`, `*`. -/
noncomputable def equivK : GF128 ≃ K := Equiv.ofBijective _ eval_bijective

lemma equivK_apply (a : GF128) : equivK a = eval (AdjoinRoot.root modulus) a := rfl

lemma equivK_zero : equivK 0 = 0 := by
  rw [equivK_apply, show (0 : GF128) = ⟨0, 0⟩ from rfl, eval, wordSum_zero]; ring

lemma equivK_one : equivK 1 = 1 := by rw [equivK_apply]; exact eval_one

lemma equivK_add (a b : GF128) : equivK (a + b) = equivK a + equivK b := by
  simp only [equivK_apply]; exact eval_add isRoot_root a b

lemma equivK_mul (a b : GF128) : equivK (a * b) = equivK a * equivK b := by
  simp only [equivK_apply]; exact eval_mul isRoot_root a b

/-- **`GF128` is a field**: the operations of `GF.lean` (`+`, `*`, `0`, `1`), with the remaining
structure (negation, inverse, casts, …) transported from `K` along `equivK`. -/
noncomputable instance instField : Field GF128 :=
  letI : Neg GF128 := ⟨fun a => equivK.symm (-equivK a)⟩
  letI : Sub GF128 := ⟨fun a b => equivK.symm (equivK a - equivK b)⟩
  letI : Inv GF128 := ⟨fun a => equivK.symm (equivK a)⁻¹⟩
  letI : Div GF128 := ⟨fun a b => equivK.symm (equivK a / equivK b)⟩
  letI : SMul ℕ GF128 := ⟨fun n a => equivK.symm (n • equivK a)⟩
  letI : SMul ℤ GF128 := ⟨fun n a => equivK.symm (n • equivK a)⟩
  letI : SMul ℚ≥0 GF128 := ⟨fun q a => equivK.symm (q • equivK a)⟩
  letI : SMul ℚ GF128 := ⟨fun q a => equivK.symm (q • equivK a)⟩
  letI : Pow GF128 ℕ := ⟨fun a n => equivK.symm (equivK a ^ n)⟩
  letI : Pow GF128 ℤ := ⟨fun a n => equivK.symm (equivK a ^ n)⟩
  letI : NatCast GF128 := ⟨fun n => equivK.symm n⟩
  letI : IntCast GF128 := ⟨fun n => equivK.symm n⟩
  letI : NNRatCast GF128 := ⟨fun q => equivK.symm q⟩
  letI : RatCast GF128 := ⟨fun q => equivK.symm q⟩
  have h : ∀ x, equivK (equivK.symm x) = x := equivK.apply_symm_apply
  Function.Injective.field equivK equivK.injective
    equivK_zero equivK_one equivK_add equivK_mul (fun _ => h _) (fun _ _ => h _)
    (fun _ => h _) (fun _ _ => h _) (fun _ _ => h _) (fun _ _ => h _) (fun _ _ => h _)
    (fun _ _ => h _) (fun _ _ => h _) (fun _ _ => h _) (fun _ => h _) (fun _ => h _)
    (fun _ => h _) (fun _ => h _)

/-- **`GF128 ≃+* GF(2)[X]/(X¹²⁸ + X⁷ + X² + X + 1)`.** -/
noncomputable def ringEquivK : GF128 ≃+* K :=
  { equivK with
    map_mul' := equivK_mul
    map_add' := equivK_add }

lemma ringEquivK_apply (a : GF128) : ringEquivK a = eval (AdjoinRoot.root modulus) a := rfl

end GF128

end VoleMole.Arith
