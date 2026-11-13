import VoleMole.Arith.Keccak

/-!
# The ripple-carry adder of Ratatouille spend (`src/ratatouille/spend.hpp:186-213`)

`addCredits a b off` is `qs_add_credits(qs, a, b, wit_off_carries)`: the bits of the summands
are given by `a i`, `b i` (witness bits or public constants), and the carries `k₁, …, k₆₄` are the
witness bits `8 off + i`. It adds the 64 constraints `aᵢbᵢ + aᵢkᵢ + bᵢkᵢ + kᵢ₊₁` (with the constant
`k₀ = poly1(0)`) and returns the 65 sum bits `aᵢ + bᵢ + kᵢ` (`i < 64`) and `k₆₄`.

Lemma 4.1 of `lean/docs/extraction/L7-keccak.md`: `addCredits_sound` (at a bit vector, the
constraints force `Σ σᵢ 2ⁱ = A + B` over ℕ, with no wrap) and `addCredits_complete` (the honest
carries satisfy them). The relation-level conservation argument (`t + x = t' + d`) is left to the
relation (`spend.hpp:363-365`): equal sum bits give equal sums by `addCredits_sound`.
-/

set_option linter.unusedSectionVars false

namespace VoleMole.Arith.Adder

open VoleMole.Arith VoleMole.Arith.Keccak

variable {F : Type*}

/-- The number of bits of a credit value (`CREDIT_BITS`). -/
def creditBits : ℕ := 64

/-- The carry `kᵢ`: the constant `0` for `i = 0`, else witness bit `8 off + i - 1`. -/
def carry [Zero F] (off i : ℕ) : Expr F := if i = 0 then Expr.const 0 else Expr.wit (8 * off + (i - 1))

/-- `qs_add_credits(qs, a, b, off)` (`spend.hpp:194-212`): the 64 carry constraints and the 65 sum
bits. -/
def addCredits [Zero F] (a b : ℕ → Expr F) (off : ℕ) : System F × Vector (Expr F) 65 :=
  ((List.range 64).map fun i =>
      a i * b i + a i * carry off i + b i * carry off i + Expr.wit (8 * off + i),
    Vector.ofFn fun i : Fin 65 => if i.1 < 64 then a i + b i + carry off i else carry off 64)

section Bits

variable [Field F] [CharP F 2]

/-- The carries of a bit vector: `k₀ = 0`, `kᵢ₊₁ = w (8 off + i)`. -/
def carryB (w : ℕ → Bool) (off i : ℕ) : Bool := if i = 0 then false else w (8 * off + (i - 1))

/-- The value of the first `n` bits. -/
def val (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => val f n + (f n).toNat * 2 ^ n

theorem eval_carry (w : ℕ → Bool) (off i : ℕ) :
    (carry (F := F) off i).eval (ofBits w) = bitF (carryB w off i) := by
  unfold carry carryB; split_ifs <;> simp [ofBits, bitF]

/-- One full adder: `a + b + k = σ + 2 maj(a, b, k)`. -/
theorem full_adder (a b k : Bool) :
    a.toNat + b.toNat + k.toNat =
      (xor (xor a b) k).toNat + 2 * ((a && b) ^^ (a && k) ^^ (b && k)).toNat := by
  cases a <;> cases b <;> cases k <;> rfl

theorem carryB_succ (w : ℕ → Bool) (off i : ℕ) : carryB w off (i + 1) = w (8 * off + i) := by
  simp [carryB]

/-- The sum bits of a bit vector: `aᵢ ⊕ bᵢ ⊕ kᵢ` for `i < 64`, and `k₆₄`. -/
def sumB (A B w : ℕ → Bool) (off i : ℕ) : Bool :=
  if i < 64 then xor (xor (A i) (B i)) (carryB w off i) else carryB w off 64

theorem constraint_iff (a b : ℕ → Expr F) (A B : ℕ → Bool) (w : ℕ → Bool) (off i : ℕ)
    (ha : (a i).eval (ofBits w) = bitF (A i)) (hb : (b i).eval (ofBits w) = bitF (B i)) :
    (a i * b i + a i * carry off i + b i * carry off i + Expr.wit (8 * off + i)).eval (ofBits w)
      = 0 ↔ carryB w off (i + 1) =
        ((A i && B i) ^^ (A i && carryB w off i) ^^ (B i && carryB w off i)) := by
  simp only [Expr.eval_add, Expr.eval_mul, Expr.eval_wit, ha, hb, eval_carry]
  rw [show ofBits w (8 * off + i) = (bitF (carryB w off (i + 1)) : F) by
    simp [ofBits, carryB_succ]]
  rw [← bitF_and, ← bitF_and, ← bitF_and, ← bitF_xor, ← bitF_xor, ← bitF_xor, bitF_eq_zero_iff]
  generalize carryB w off (i + 1) = k'
  cases k' <;> simp

/-- Lemma 4.1 (`L7-keccak.md` §4.4): if the carry constraints hold at a bit vector, the 65 sum
bits are the bits `sumB` and `Σ σᵢ 2ⁱ = A + B` over ℕ. -/
theorem addCredits_sound (a b : ℕ → Expr F) (A B : ℕ → Bool) (w : ℕ → Bool) (off : ℕ)
    (ha : ∀ i < 64, (a i).eval (ofBits w) = bitF (A i))
    (hb : ∀ i < 64, (b i).eval (ofBits w) = bitF (B i))
    (hs : (addCredits a b off).1.Holds (ofBits w)) :
    (∀ i (hi : i < 65), (addCredits a b off).2[i].eval (ofBits w) = bitF (sumB A B w off i)) ∧
      val (sumB A B w off) 65 = val A 64 + val B 64 := by
  have hk : ∀ i < 64, carryB w off (i + 1) =
      ((A i && B i) ^^ (A i && carryB w off i) ^^ (B i && carryB w off i)) := fun i hi =>
    (constraint_iff a b A B w off i (ha i hi) (hb i hi)).1
      (hs _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))
  refine ⟨fun i hi => ?_, ?_⟩
  · simp only [addCredits, Vector.getElem_ofFn, sumB]
    split_ifs with h
    · simp [ha i h, hb i h, eval_carry, bitF_xor, add_assoc]
    · exact eval_carry w off 64
  · have key : ∀ n ≤ 64, val (sumB A B w off) n + (carryB w off n).toNat * 2 ^ n =
        val A n + val B n := by
      intro n hn
      induction n with
      | zero => simp [val, carryB]
      | succ n ih =>
        have h := full_adder (A n) (B n) (carryB w off n)
        rw [← hk n (by omega)] at h
        have h' := congrArg (· * 2 ^ n) h
        simp only [add_mul] at h'
        have ih' := ih (by omega)
        simp only [val, sumB, show n < 64 by omega, ite_true, pow_succ]
        linarith
    have h64 := key 64 le_rfl
    have e : val (sumB A B w off) 65 =
        val (sumB A B w off) 64 + (sumB A B w off 64).toNat * 2 ^ 64 := rfl
    have e' : sumB A B w off 64 = carryB w off 64 := by simp [sumB]
    rw [e, e', h64]

/-- Completeness: the honest carries (`kᵢ₊₁ = maj(aᵢ, bᵢ, kᵢ)`) satisfy the constraints. -/
theorem addCredits_complete (a b : ℕ → Expr F) (A B : ℕ → Bool) (w : ℕ → Bool) (off : ℕ)
    (ha : ∀ i < 64, (a i).eval (ofBits w) = bitF (A i))
    (hb : ∀ i < 64, (b i).eval (ofBits w) = bitF (B i))
    (hk : ∀ i < 64, carryB w off (i + 1) =
      ((A i && B i) ^^ (A i && carryB w off i) ^^ (B i && carryB w off i))) :
    (addCredits a b off).1.Holds (ofBits w) := by
  intro e he
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 he
  have hi := List.mem_range.1 hi
  exact (constraint_iff a b A B w off i (ha i hi) (hb i hi)).2 (hk i hi)

end Bits

end VoleMole.Arith.Adder
