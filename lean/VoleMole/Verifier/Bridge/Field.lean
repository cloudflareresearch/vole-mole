import VoleMole.Verifier.QuickSilver
import VoleMole.Seed.QuickSilver
import VoleMole.Seed.KOS

/-!
# Bridge: the executable `GF128` arithmetic, seen in an abstract field

The executable verifier computes in `Arith.GF128` (`+` = XOR, `*` = carry-less product mod
`X¹²⁸ + X⁷ + X² + X + 1`), for which `Arith/GF.lean` deliberately proves no `Field` instance. The
models (`Seed/*`, `EndToEnd/*`) are stated over an arbitrary `[Field F]`. To connect them without
re-proving the field axioms for `GF128`, the bridge theorems take a **field embedding**
`φ : GF128 → F` (`GFEmbedding`): an injective map preserving `1`, `+` and `*`. Every statement
about the executable code is then of the form "`φ` of what the verifier computes is the model's
quantity at the `φ`-images".

**Assumed, not proved:** that such an embedding into a field with `2¹²⁸` elements exists, i.e.
that `GF128`'s operations make it the field GF(2¹²⁸) (`X¹²⁸ + X⁷ + X² + X + 1` irreducible and the
multiplication loop correct). `lake exe arith_vectors` checks `GF128.mul` against the C++, and
`Arith/GF.lean` proves bilinearity and `1 * b = b`, but associativity, commutativity and inverses
are not proved.

Results (all for any embedding `φ`):
* `map_horner`: `φ (horner key xs) = Seed.horner (φ key) n (φ ∘ xs)` (the executable Horner fold
  is the model's Horner recursion), and `map_horner_eq_eval`: it is `(hornerPoly (φ ∘ xs)).eval`
  (`Seed/KOS.lean`'s VOLEHash polynomial);
* `map_horner_eq_blockedHash`: it is also the C++'s blocked hash `Seed.blockedHash`, which
  `Seed.zkHash_eq_code` relates to the ZKHash;
* `map_gfPow`: `φ (gfPow a n) = (φ a)^n`;
* `map_gfInv`: if `F` has `2¹²⁸` elements, `φ (gfInv a) = (φ a)⁻¹` (Fermat).
-/

namespace VoleMole.Verifier.Bridge

open VoleMole.Arith VoleMole.Verifier

/-- An embedding of the executable `GF128` into a field. -/
structure GFEmbedding (F : Type*) [Field F] where
  toFun : GF128 → F
  map_one : toFun 1 = 1
  map_add : ∀ a b, toFun (a + b) = toFun a + toFun b
  map_mul : ∀ a b, toFun (a * b) = toFun a * toFun b
  injective : Function.Injective toFun

namespace GFEmbedding

variable {F : Type*} [Field F] (φ : GFEmbedding F)

instance : CoeFun (GFEmbedding F) (fun _ => GF128 → F) := ⟨GFEmbedding.toFun⟩

@[simp] lemma map_add' (a b : GF128) : φ (a + b) = φ a + φ b := φ.map_add a b
@[simp] lemma map_mul' (a b : GF128) : φ (a * b) = φ a * φ b := φ.map_mul a b
@[simp] lemma map_one' : φ 1 = 1 := φ.map_one

@[simp] lemma map_zero : φ 0 = 0 := by
  have h : φ (0 + 0) = φ 0 + φ 0 := φ.map_add 0 0
  have h0 : (0 : GF128) + 0 = 0 := rfl
  rw [h0] at h
  exact left_eq_add.1 h

lemma map_eq_zero_iff (a : GF128) : φ a = 0 ↔ a = 0 :=
  ⟨fun h => φ.injective (h.trans φ.map_zero.symm), fun h => h ▸ φ.map_zero⟩

/-- The Horner fold of the executable code from any start value. -/
lemma map_foldl_horner (key : GF128) : ∀ (l : List GF128) (acc : GF128),
    φ (l.foldl (fun s x => s * key + x) acc) =
      φ acc * φ key ^ l.length +
        ∑ k : Fin l.length, φ key ^ (l.length - 1 - (k : ℕ)) * φ (l.get k)
  | [], acc => by simp
  | x :: l, acc => by
      rw [List.foldl_cons, map_foldl_horner key l]
      simp only [List.length_cons]
      rw [Fin.sum_univ_succ]
      simp only [map_add', map_mul', List.get_eq_getElem, Fin.val_zero,
        Fin.val_succ, List.getElem_cons_zero, List.getElem_cons_succ]
      have hsum : ∑ i : Fin l.length, φ key ^ (l.length + 1 - 1 - ((i : ℕ) + 1)) * φ l[(i : ℕ)] =
          ∑ i : Fin l.length, φ key ^ (l.length - 1 - (i : ℕ)) * φ l[(i : ℕ)] :=
        Finset.sum_congr rfl fun i _ => by congr 2; omega
      rw [hsum, show l.length + 1 - 1 - 0 = l.length by omega, pow_succ]
      ring

/-- **The executable Horner hash is the model's.** -/
theorem map_horner (key : GF128) (xs : Array GF128) :
    φ (horner key xs) = Seed.horner (φ key) xs.size (fun k => φ xs[k]) := by
  rw [Seed.horner_eq_sum, horner, ← Array.foldl_toList, map_foldl_horner, φ.map_zero, zero_mul,
    zero_add]
  exact Fintype.sum_equiv (finCongr (by simp)) _ _ fun k => by simp

/-- The executable Horner hash is `Seed/KOS.lean`'s `hornerPoly` evaluated at the key. -/
theorem map_horner_eq_eval [Fintype F] [DecidableEq F] (key : GF128) (xs : Array GF128) :
    φ (horner key xs) = (Seed.hornerPoly (fun k : Fin xs.size => φ xs[k])).eval (φ key) := by
  rw [map_horner, Seed.horner_eq_sum, Seed.eval_hornerPoly]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- The executable Horner hash is also the C++'s blocked `uhasher_gfsecpar` (`Seed.blockedHash`,
`PREP_KEY_POWS = 8`) on the same inputs, so the plain fold computes what `finalize_hashes` combines
(`Seed.zkHash_eq_code`). -/
theorem map_horner_eq_blockedHash (key : GF128) (xs : Array GF128) (hn : 0 < xs.size) :
    φ (horner key xs) = Seed.blockedHash (φ key) (xs.toList.map φ) := by
  rw [Seed.blockedHash_eq_sum _ _ (by rw [← List.length_pos_iff]; simpa using hn), map_horner,
    Seed.horner_eq_sum]
  exact Fintype.sum_equiv (finCongr (by simp)) _ _ fun k => by simp

/-- `gfPow` is the power. -/
theorem map_gfPow (a : GF128) (n : ℕ) : φ (gfPow a n) = φ a ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [gfPow]
    by_cases h0 : n = 0
    · simp [h0]
    have ih' := ih (n / 2) (by omega)
    simp only [h0, ite_false]
    have hn : n = n / 2 + n / 2 + n % 2 := by omega
    split_ifs with h1
    · rw [map_mul', map_mul', ih']
      conv_rhs => rw [hn, h1, pow_add, pow_add, pow_one]
    · rw [map_mul', ih']
      conv_rhs => rw [hn, show n % 2 = 0 by omega, add_zero, pow_add]

/-- `gfInv` is the inverse in a field of `2¹²⁸` elements (and `0 ↦ 0`). -/
theorem map_gfInv [Fintype F] (hF : Fintype.card F = 2 ^ 128) (a : GF128) :
    φ (gfInv a) = (φ a)⁻¹ := by
  rw [gfInv, map_gfPow]
  by_cases ha : φ a = 0
  · rw [ha, inv_zero, zero_pow (by norm_num)]
  · have h1 := FiniteField.pow_card_sub_one_eq_one (φ a) ha
    rw [hF] at h1
    refine (eq_inv_of_mul_eq_one_left ?_)
    rw [← pow_succ, show 2 ^ 128 - 2 + 1 = 2 ^ 128 - 1 by norm_num, h1]

end GFEmbedding

end VoleMole.Verifier.Bridge
