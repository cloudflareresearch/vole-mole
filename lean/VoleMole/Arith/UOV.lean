import VoleMole.Arith.Basic
import VoleMole.SeedExtraction

/-!
# The UOV gadget: `l(P(s))` on committed bytes (`src/uov/circuit.hpp`)

An executable model of `uov::detail::qs_eval_combined_public_map` (`src/uov/circuit.hpp:114-137`)
and of the monomial enumeration `for_each_monomial` (`src/uov/public_key.hpp:45-63`) it uses, with
soundness and completeness proofs. This mechanizes Lemma 1's consequences and Claim 2a of
`lean/docs/extraction/L7-uov.md`. `publicMap` below is *defined* by `for_each_monomial`'s layout;
Claim 2b (it equals pqov's `ov_publicmap`) is `Pqov.ovPublicmap_eq_publicMap` (`Arith/Pqov.lean`).

## Model

* `F` is the QuickSilver field (GF(2¹²⁸) in the code). The generator needs only `+`, `*`, `0`, `1`
  on `F`, so it can be run on a concrete GF(2¹²⁸) without a `Field` instance; the theorems assume
  `[Field F] [CharP F 2]`.
* `K` is GF(256), abstract: only `+`, `*`, `0`, a bit decomposition `toBits : K → Fin 8 → Bool`
  (byte `a` ↦ its bits, LSB first) and a decoder `ofByte : (Fin 8 → Bool) → K`.
* `β : Fin 8 → F` are the embedding constants (`β 0 = 1`, `β b = gf8_in_gf128[b-1]`), and
  `ι = embed β ∘ toBits` is `uov::detail::embed` (`circuit.hpp:35-37`). The hypothesis
  `IsEmbedding β toBits ofByte` says `ι` is an injective homomorphism and `ofByte` is a right
  inverse of `toBits`; the differential-test worker checks it exhaustively on the concrete fields.
* The public key is its expanded byte array `pk : ℕ → K` (`PublicKeyAccess::expanded`): the
  coefficient of monomial `m` in component `k` is `pk (m.off + k)`.
* The combination coefficients are `l : Fin M → F`. `Combination::combine` (`circuit.hpp:79-85`)
  is modelled by its value `Σ_k l_k ι(a_k)` (`combineVec`): its tables hold `l_k ι(a)`
  (L7-uov.md, Corollary of Lemma 1), and the constant enters the expression only as a value.

## Main results

* `eval_evalCombinedPublicMap` (Claim 2a, any committed values): the gadget's value is
  `Σ_k l_k · component k x` with `component k x = Σ_m ι(p^k_m) x_i x_j` independent of `l`.
* `eval_evalCombinedPublicMap_bits` / `_of_bits`: on bytes loaded from a bit vector (or from
  committed values that are bits on the `8N` bits of `s`), it is `Σ_k l_k ι(P(σ)_k)`.
* `degree_evalCombinedPublicMap`: degree `≤ 2` on degree-`≤ 1` inputs.
* `uovSystem` (bit constraints on `s` and the single constraint `l(P(s)) + l(t) = 0`, the PomFRIT
  shape without `r`), with `uov_complete`, `uov_holds_iff`, `uov_sound` (arbitrary `w ∈ F^ℓ`), and
  the combination step `uov_card_bad` / `uov_bad_prob` (`P(σ) ≠ t` ⇒ density `1/|F|` of bad `l`).
-/

open Finset

set_option linter.unusedSectionVars false

namespace VoleMole.Arith.UOV

/-! ## The expanded public key layout (`src/uov/public_key.hpp`) -/

section Layout

/-- `triangle(n) = n(n+1)/2` (`public_key.hpp:18`). -/
def triangle (n : ℕ) : ℕ := n * (n + 1) / 2

/-- One call `f(i, j, coeffs)` of `for_each_monomial`: the monomial `x_i x_j` and the offset of
its `M` coefficients in the expanded key. -/
structure Monomial where
  i : ℕ
  j : ℕ
  off : ℕ
  deriving DecidableEq, Repr

/-- The inner loop `for (j = j0; j < n; ++j, p += M) f(i, j, p)`, starting at pointer `p`. -/
def row (M i j0 n p : ℕ) : List Monomial :=
  (List.range (n - j0)).map fun t => ⟨i, j0 + t, p + t * M⟩

/-- `for_each_monomial` (`public_key.hpp:45-63`) with `V = N - M` (`:15`). The pointers `p1`,
`p2`, `p3` are given in closed form at the start of each row: P1 row `i` starts after
`Σ_{i'<i} (V - i')` vectors, P2 row `i` after `i (N - V)` vectors, and P3 row `i` after
`Σ_{V ≤ i' < i} (N - i')` vectors; `p2 = p1 + M·triangle(V)`, `p3 = p2 + M·V·M` (`:47-49`). -/
def forEachMonomial (N M : ℕ) : List Monomial :=
  let V := N - M
  let p2 := M * triangle V
  let p3 := p2 + M * V * M
  (List.range V).flatMap (fun i =>
      row M i i V (M * (triangle V - triangle (V - i))) ++ row M i V N (p2 + i * ((N - V) * M))) ++
    (List.range' V (N - V)).flatMap fun i =>
      row M i i N (p3 + M * (triangle (N - V) - triangle (N - i)))

theorem mem_forEachMonomial {N M : ℕ} {m : Monomial} (h : m ∈ forEachMonomial N M) :
    m.i ≤ m.j ∧ m.j < N := by
  simp only [forEachMonomial, row, List.mem_append, List.mem_flatMap, List.mem_range,
    List.mem_range', List.mem_map] at h
  rcases h with ⟨a, ha, ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩⟩ | ⟨a, ha, t, ht, rfl⟩ <;> dsimp only <;> omega

/-- The (i, j) pairs in visiting order: all `i ≤ j < N`, row by row. -/
def lexPairs (N : ℕ) : List (ℕ × ℕ) :=
  (List.range N).flatMap fun i => (List.range' i (N - i)).map fun j => (i, j)

/-- A literal transcription of `for_each_monomial` with the running pointers `p1`, `p2`, `p3`
(`public_key.hpp:47-62`), used only to check the closed-form offsets of `forEachMonomial`. -/
def forEachMonomialPtr (N M : ℕ) : List Monomial :=
  let V := N - M
  let st := (List.range V).foldl (fun (st : List Monomial × ℕ × ℕ) i =>
      (st.1 ++ row M i i V st.2.1 ++ row M i V N st.2.2, st.2.1 + (V - i) * M,
        st.2.2 + (N - V) * M)) ([], 0, M * triangle V)
  let st3 := (List.range' V (N - V)).foldl (fun (st : List Monomial × ℕ) i =>
      (st.1 ++ row M i i N st.2, st.2 + (N - i) * M)) ([], M * triangle V + M * V * M)
  st.1 ++ st3.1

/-! Sanity checks on small sizes: the closed-form pointers agree with the running pointers, every
pair `i ≤ j` is visited once in row order, and the offsets cover the expanded key contiguously
(`M` bytes per monomial). -/

example : forEachMonomial 5 2 = forEachMonomialPtr 5 2 := by decide
example : forEachMonomial 7 3 = forEachMonomialPtr 7 3 := by decide
example : forEachMonomial 6 1 = forEachMonomialPtr 6 1 := by decide
example : forEachMonomial 4 4 = forEachMonomialPtr 4 4 := by decide
example : (forEachMonomial 7 3).map (fun m => (m.i, m.j)) = lexPairs 7 := by decide
example : (forEachMonomial 7 3).length = triangle 7 ∧
    (List.range (triangle 7)).all fun x => (forEachMonomial 7 3).any (·.off = 3 * x) := by decide

end Layout

/-! ## The embedding and the combination (`circuit.hpp:35-37, 79-105`) -/

section Embedding

variable {F K : Type*}

/-- `from_8_byte`: `Σ_b a_b β_b`, i.e. `ι` on the bits `a` of a byte. -/
def embed [Add F] [Mul F] [Zero F] [One F] (β : Fin 8 → F) (a : Fin 8 → Bool) : F :=
  bitF (a 0) * β 0 + bitF (a 1) * β 1 + bitF (a 2) * β 2 + bitF (a 3) * β 3 +
    bitF (a 4) * β 4 + bitF (a 5) * β 5 + bitF (a 6) * β 6 + bitF (a 7) * β 7

theorem embed_eq [CommRing F] (β : Fin 8 → F) (a : Fin 8 → Bool) :
    embed β a = ∑ b : Fin 8, β b * bitF (a b) := by
  simp only [embed, Fin.sum_univ_eight]; ring

/-- The hypotheses on the GF(256) model: `ι := embed β ∘ toBits` is an injective homomorphism
(L7-uov.md Lemma 1(b), checked exhaustively by the harness), and `ofByte` decodes bits. -/
structure IsEmbedding [Add F] [Mul F] [Zero F] [One F] [Add K] [Mul K] [Zero K]
    (β : Fin 8 → F) (toBits : K → Fin 8 → Bool) (ofByte : (Fin 8 → Bool) → K) : Prop where
  toBits_ofByte : ∀ v, toBits (ofByte v) = v
  map_zero : embed β (toBits 0) = 0
  map_add : ∀ a b, embed β (toBits (a + b)) = embed β (toBits a) + embed β (toBits b)
  map_mul : ∀ a b, embed β (toBits (a * b)) = embed β (toBits a) * embed β (toBits b)
  injective : Function.Injective fun a => embed β (toBits a)

/-- `Combination::combine(a) = Σ_k l_k ι(a_k)` (`circuit.hpp:79-85`), summed left to right. Also
`lh` in PomFRIT redeem (`src/pomfrit/redeem.hpp:135-141`). -/
def combineVec [Add F] [Mul F] [Zero F] [One F] {M : ℕ} (β : Fin 8 → F) (toBits : K → Fin 8 → Bool)
    (l : Fin M → F) (a : Fin M → K) : F :=
  (List.finRange M).foldl (fun acc k => acc + l k * embed β (toBits (a k))) 0

theorem foldl_add_eq {α : Type*} [AddCommMonoid F] (f : α → F) (L : List α) (a : F) :
    L.foldl (fun acc x => acc + f x) a = a + (L.map f).sum := by
  induction L generalizing a with
  | nil => simp
  | cons x L ih => simp [ih, add_assoc]

theorem combineVec_eq [CommRing F] {M : ℕ} (β : Fin 8 → F) (toBits : K → Fin 8 → Bool)
    (l : Fin M → F) (a : Fin M → K) :
    combineVec β toBits l a = ∑ k, l k * embed β (toBits (a k)) := by
  rw [combineVec, foldl_add_eq, zero_add, Fin.sum_univ_def]

end Embedding

/-! ## The generator (`qs_eval_combined_public_map`, `circuit.hpp:114-137`) -/

section Generator

variable {F K : Type*} [Add F] [Mul F] [Zero F] [One F]

/-- The loop state `(y, row, current_i)`. -/
abbrev EvalState (F : Type*) := Expr F × Expr F × ℕ

/-- The loop body (`circuit.hpp:127-133`), with `c m = l.combine(coeffs)`:
```
if (i != current_i) { y += s[current_i] * row; row = zero_1; current_i = i; }
row += l.combine(coeffs) * s[j];
``` -/
def evalStep (c : Monomial → F) (s : ℕ → Expr F) (zero1 : Expr F) (st : EvalState F)
    (m : Monomial) : EvalState F :=
  if m.i = st.2.2 then (st.1, st.2.1 + Expr.const (c m) * s m.j, st.2.2)
  else (st.1 + s st.2.2 * st.2.1, zero1 + Expr.const (c m) * s m.j, m.i)

/-- `qs_eval_combined_public_map(pk, s, l)`: `zero_1 = s[0] + s[0]`, `y = zero_1 * zero_1`,
`row = zero_1`, the loop over `for_each_monomial`, and the final `y += s[current_i] * row`.

Arguments: the embedding constants `β`, the byte decomposition `toBits` of GF(256), the sizes `N`
(variables) and `M` (equations), the expanded public key `pk`, the committed variables `s` (in the
protocols `s i = byteLoad β (WIT_OFF_S + i)`), and the combination coefficients `l`. -/
def evalCombinedPublicMap (β : Fin 8 → F) (toBits : K → Fin 8 → Bool) (N M : ℕ) (pk : ℕ → K)
    (s : ℕ → Expr F) (l : Fin M → F) : Expr F :=
  let zero1 := s 0 + s 0
  let st := (forEachMonomial N M).foldl
    (evalStep (fun m => combineVec β toBits l fun k => pk (m.off + k)) s zero1)
    (zero1 * zero1, zero1, 0)
  st.1 + s st.2.2 * st.2.1

/-- `Σ_k l_k · T_k` accumulated as `acc = 0; acc += l.coeff(k) * T_k` (e.g. `lr` in PomFRIT redeem,
`lout`/`ly` with `T_k = qs_byte(out, k)` in Moussaka/Ratatouille). -/
def linComb {M : ℕ} (l : Fin M → F) (T : Fin M → Expr F) : Expr F :=
  (List.finRange M).foldl (fun acc k => acc + Expr.const (l k) * T k) (Expr.const 0)

/-- The decoded GF(256) variables: `σ_i` is the byte at witness byte offset `o + i`. -/
def decode (ofByte : (Fin 8 → Bool) → K) (w : ℕ → Bool) (o : ℕ) : ℕ → K :=
  fun i => ofByte fun b => w (8 * (o + i) + b)

end Generator

/-! ## The public map (the relation side) -/

section Spec

variable {F K : Type*}

/-- `P(σ)_k = Σ_m p^k_m σ_i σ_j` over `K`, with monomials and coefficients read by
`for_each_monomial` (`public_key.hpp:36-39`). Claim 2b of L7-uov.md identifies it with pqov's
`ov_publicmap` (`Pqov.ovPublicmap_eq_publicMap`). -/
def publicMap [Add K] [Mul K] [Zero K] (N M : ℕ) (pk : ℕ → K) (σ : ℕ → K) (k : Fin M) : K :=
  ((forEachMonomial N M).map fun m => pk (m.off + k) * σ m.i * σ m.j).sum

/-- The `l`-independent component `E_k(x) = Σ_m ι(p^k_m) x_i x_j` of the gadget (L7-uov.md §2). -/
def component [Add F] [Mul F] [Zero F] [One F] (β : Fin 8 → F) (toBits : K → Fin 8 → Bool)
    (N M : ℕ) (pk : ℕ → K) (k : Fin M) (x : ℕ → F) : F :=
  ((forEachMonomial N M).map fun m => embed β (toBits (pk (m.off + k))) * x m.i * x m.j).sum

end Spec

/-! ## Claim 2a: the value of the gadget -/

section Value

variable {F K : Type*} [Field F] [CharP F 2]

/-- Swap a list sum and a finite sum. -/
theorem sum_list_sum_comm {α ι : Type*} [Fintype ι] (L : List α) (f : α → ι → F) :
    ∑ k, (L.map fun a => f a k).sum = (L.map fun a => ∑ k, f a k).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [Finset.sum_add_distrib, ih]

/-- The loop invariant: `y + s[current_i] · row` is the sum over the visited monomials. -/
theorem foldl_evalStep (c : Monomial → F) (s : ℕ → Expr F) (zero1 : Expr F) (w : ℕ → F)
    (h0 : zero1.eval w = 0) (L : List Monomial) (st : EvalState F) :
    let st' := L.foldl (evalStep c s zero1) st
    st'.1.eval w + (s st'.2.2).eval w * st'.2.1.eval w =
      st.1.eval w + (s st.2.2).eval w * st.2.1.eval w +
        (L.map fun m => (s m.i).eval w * (c m * (s m.j).eval w)).sum := by
  induction L generalizing st with
  | nil => simp
  | cons m L ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih]
    unfold evalStep
    split_ifs with h
    · simp only [Expr.eval_add, Expr.eval_mul, Expr.eval_const, h]; ring
    · simp only [Expr.eval_add, Expr.eval_mul, Expr.eval_const, h0]; ring

theorem eval_evalCombinedPublicMap_sum (β : Fin 8 → F) (toBits : K → Fin 8 → Bool) (N M : ℕ)
    (pk : ℕ → K) (s : ℕ → Expr F) (l : Fin M → F) (w : ℕ → F) :
    (evalCombinedPublicMap β toBits N M pk s l).eval w =
      ((forEachMonomial N M).map fun m =>
        (s m.i).eval w *
          (combineVec β toBits l (fun k => pk (m.off + k)) * (s m.j).eval w)).sum := by
  have h0 : (s 0 + s 0).eval w = 0 := by simp [CharTwo.add_self_eq_zero]
  have := foldl_evalStep (fun m => combineVec β toBits l fun k => pk (m.off + k)) s (s 0 + s 0)
    w h0 (forEachMonomial N M) ((s 0 + s 0) * (s 0 + s 0), s 0 + s 0, 0)
  simp only [Expr.eval_mul, h0, mul_zero, zero_add] at this
  simp only [evalCombinedPublicMap, Expr.eval_add, Expr.eval_mul]
  exact this

/-- **Claim 2a.** For any committed values, the gadget's value is `Σ_k l_k E_k(x)` with
`x_i = s_i(w)` and `E_k = component k` independent of `l`. -/
theorem eval_evalCombinedPublicMap (β : Fin 8 → F) (toBits : K → Fin 8 → Bool) (N M : ℕ)
    (pk : ℕ → K) (s : ℕ → Expr F) (l : Fin M → F) (w : ℕ → F) :
    (evalCombinedPublicMap β toBits N M pk s l).eval w =
      ∑ k, l k * component β toBits N M pk k (fun i => (s i).eval w) := by
  rw [eval_evalCombinedPublicMap_sum]
  simp only [component, ← List.sum_map_mul_left]
  rw [sum_list_sum_comm]
  congr 1
  refine List.map_congr_left fun m _ => ?_
  rw [combineVec_eq, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem eval_linComb {M : ℕ} (l : Fin M → F) (T : Fin M → Expr F) (w : ℕ → F) :
    (linComb l T).eval w = ∑ k, l k * (T k).eval w := by
  have : ∀ (L : List (Fin M)) (a : Expr F),
      (L.foldl (fun acc k => acc + Expr.const (l k) * T k) a).eval w =
        a.eval w + (L.map fun k => l k * (T k).eval w).sum := by
    intro L
    induction L with
    | nil => simp
    | cons k L ih => intro a; simp [ih, add_assoc]
  rw [linComb, this, Fin.sum_univ_def]; simp

end Value

/-! ## On bit vectors: `ι(P(σ))` -/

section Bits

variable {F K : Type*} [Field F] [CharP F 2] [Add K] [Mul K] [Zero K]
variable {β : Fin 8 → F} {toBits : K → Fin 8 → Bool} {ofByte : (Fin 8 → Bool) → K}

/-- A byte loaded from a bit vector is `ι` of the decoded byte (L7-uov.md Lemma 1(a)). -/
theorem eval_byteLoad_bits (hι : IsEmbedding β toBits ofByte) (w : ℕ → Bool) (o i : ℕ) :
    (byteLoad β (o + i)).eval (ofBits w) = embed β (toBits (decode ofByte w o i)) := by
  rw [eval_byteLoad, decode, hι.toBits_ofByte, embed_eq]
  rfl

/-- `ι` commutes with the public map: `E_k(ι ∘ σ) = ι(P(σ)_k)`. -/
theorem component_embed (hι : IsEmbedding β toBits ofByte) (N M : ℕ) (pk : ℕ → K) (σ : ℕ → K)
    (k : Fin M) :
    component β toBits N M pk k (fun i => embed β (toBits (σ i))) =
      embed β (toBits (publicMap N M pk σ k)) := by
  simp only [component, publicMap]
  induction forEachMonomial N M with
  | nil => simp [hι.map_zero]
  | cons m L ih => simp [List.map_cons, List.sum_cons, hι.map_add, hι.map_mul, ih]

/-- The gadget on bytes loaded from a bit vector: `Σ_k l_k ι(P(σ)_k)`. -/
theorem eval_evalCombinedPublicMap_bits (hι : IsEmbedding β toBits ofByte) (N M : ℕ) (pk : ℕ → K)
    (l : Fin M → F) (w : ℕ → Bool) (o : ℕ) :
    (evalCombinedPublicMap β toBits N M pk (fun i => byteLoad β (o + i)) l).eval (ofBits w) =
      ∑ k, l k * embed β (toBits (publicMap N M pk (decode ofByte w o) k)) := by
  rw [eval_evalCombinedPublicMap]
  simp only [eval_byteLoad_bits hι, component_embed hι]

/-- Changing committed values outside the `N` loaded bytes does not change the gadget's value. -/
theorem eval_evalCombinedPublicMap_congr (β : Fin 8 → F) (toBits : K → Fin 8 → Bool) (N M : ℕ)
    (pk : ℕ → K) (s : ℕ → Expr F) (l : Fin M → F) (w w' : ℕ → F)
    (h : ∀ i < N, (s i).eval w = (s i).eval w') :
    (evalCombinedPublicMap β toBits N M pk s l).eval w =
      (evalCombinedPublicMap β toBits N M pk s l).eval w' := by
  rw [eval_evalCombinedPublicMap_sum, eval_evalCombinedPublicMap_sum]
  congr 1
  refine List.map_congr_left fun m hm => ?_
  obtain ⟨hij, hj⟩ := mem_forEachMonomial hm
  rw [h m.i (by omega), h m.j hj]

/-- The gadget at committed values that are bits on the `8N` bits of `s` (and arbitrary
elsewhere), as in the protocols after their bit constraints: `Σ_k l_k ι(P(σ)_k)`. -/
theorem eval_evalCombinedPublicMap_of_bits (hι : IsEmbedding β toBits ofByte) (N M : ℕ)
    (pk : ℕ → K) (l : Fin M → F) (o : ℕ) (w : ℕ → F) (wb : ℕ → Bool)
    (hw : ∀ n < 8 * N, w (8 * o + n) = bitF (wb (8 * o + n))) :
    (evalCombinedPublicMap β toBits N M pk (fun i => byteLoad β (o + i)) l).eval w =
      ∑ k, l k * embed β (toBits (publicMap N M pk (decode ofByte wb o) k)) := by
  rw [← eval_evalCombinedPublicMap_bits hι]
  refine eval_evalCombinedPublicMap_congr β toBits N M pk _ l _ _ fun i hi => ?_
  simp only [eval_byteLoad]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hn : 8 * (o + i) + b = 8 * o + (8 * i + b) := by ring
  rw [hn, hw (8 * i + b) (by omega)]
  rfl

end Bits

/-! ## Degree -/

section Degree

variable {F K : Type*} [Add F] [Mul F] [Zero F] [One F]

theorem degree_add (a b : Expr F) : (a + b).degree = max a.degree b.degree := rfl
theorem degree_mul (a b : Expr F) : (a * b).degree = a.degree + b.degree := rfl

theorem degree_foldl_evalStep (c : Monomial → F) (s : ℕ → Expr F) (zero1 : Expr F)
    (hs : ∀ i, (s i).degree ≤ 1) (h0 : zero1.degree ≤ 1) (L : List Monomial) (st : EvalState F)
    (hst : st.1.degree ≤ 2 ∧ st.2.1.degree ≤ 1) :
    let st' := L.foldl (evalStep c s zero1) st
    st'.1.degree ≤ 2 ∧ st'.2.1.degree ≤ 1 := by
  induction L generalizing st with
  | nil => exact hst
  | cons m L ih =>
    refine ih _ ?_
    have := hs m.j
    have := hs st.2.2
    unfold evalStep
    split_ifs
    · refine ⟨hst.1, ?_⟩
      rw [degree_add, degree_mul]; simp only [Expr.degree]; omega
    · refine ⟨?_, ?_⟩
      · rw [degree_add, degree_mul]; omega
      · rw [degree_add, degree_mul]; simp only [Expr.degree]; omega

/-- The gadget has degree `≤ 2` on degree-`≤ 1` inputs (the C++ return type `qs_val<QS, 2>`). -/
theorem degree_evalCombinedPublicMap (β : Fin 8 → F) (toBits : K → Fin 8 → Bool) (N M : ℕ)
    (pk : ℕ → K) (s : ℕ → Expr F) (l : Fin M → F) (hs : ∀ i, (s i).degree ≤ 1) :
    (evalCombinedPublicMap β toBits N M pk s l).degree ≤ 2 := by
  have h0 : (s 0 + s 0).degree ≤ 1 := by
    have := hs 0
    simp only [degree_add] at *; omega
  have := degree_foldl_evalStep (fun m => combineVec β toBits l fun k => pk (m.off + k)) s
    (s 0 + s 0) hs h0 (forEachMonomial N M) ((s 0 + s 0) * (s 0 + s 0), s 0 + s 0, 0)
    ⟨by simp only [degree_mul] at *; omega, h0⟩
  simp only [evalCombinedPublicMap]
  generalize List.foldl _ _ _ = st at this
  have := hs st.2.2
  simp only [degree_add, degree_mul] at *
  omega

theorem degree_byteLoad (β : Fin 8 → F) (o : ℕ) : (byteLoad β o).degree = 1 := rfl

end Degree

/-! ## The self-contained system `P(s) = t` -/

section System

variable {F K : Type*}

/-- The UOV relation `P(s) = t` for a public target `t`, as the relations build it: bit
constraints on the `8N` bits of `s` (bytes `[o, o+N)`), then `l(P(s)) + l(t) = 0` with `l(t)` a
public constant (as `lp + lh` in PomFRIT redeem, `src/pomfrit/redeem.hpp:114-142`). -/
def uovSystem [Add F] [Mul F] [Zero F] [One F] (β : Fin 8 → F) (toBits : K → Fin 8 → Bool)
    (N M : ℕ) (pk : ℕ → K) (l : Fin M → F) (o : ℕ) (t : Fin M → K) : System F :=
  (List.range (8 * N)).map (fun n => bitConstraint (Expr.wit (8 * o + n))) ++
    [evalCombinedPublicMap β toBits N M pk (fun i => byteLoad β (o + i)) l +
      Expr.const (combineVec β toBits l t)]

variable [Field F] [CharP F 2] [Add K] [Mul K] [Zero K]
variable {β : Fin 8 → F} {toBits : K → Fin 8 → Bool} {ofByte : (Fin 8 → Bool) → K}

theorem bitConstraint_bits (w : ℕ → Bool) (i : ℕ) :
    (bitConstraint (Expr.wit i)).eval (ofBits w : ℕ → F) = 0 := by
  simp only [bitConstraint, Expr.eval_mul, Expr.eval_add, Expr.eval_wit, Expr.eval_const, ofBits,
    bitF]
  split_ifs <;> simp [CharTwo.add_self_eq_zero]

/-- A satisfied bit constraint `x(x+1) = 0` forces `x ∈ {0, 1}` (L7-uov.md Lemma 3). -/
theorem eq_bitF_of_bitConstraint [DecidableEq F] {w : ℕ → F} {i : ℕ}
    (h : (bitConstraint (Expr.wit i)).eval w = 0) :
    w i = bitF (decide (w i = 1)) := by
  simp only [bitConstraint, Expr.eval_mul, Expr.eval_add, Expr.eval_wit, Expr.eval_const,
    mul_eq_zero] at h
  rcases h with h | h
  · simp [bitF, h]
  · have : w i = 1 := by
      rw [← CharTwo.add_self_eq_zero (1 : F), ← sub_eq_zero] at *
      linear_combination h
    simp [bitF, this]

/-- The constraint values on a bit vector: everything vanishes iff
`Σ_k l_k (ι(P(σ)_k) + ι(t_k)) = 0`, with `σ` the decoded bytes. -/
theorem uov_holds_iff (hι : IsEmbedding β toBits ofByte) (N M : ℕ) (pk : ℕ → K) (l : Fin M → F)
    (o : ℕ) (t : Fin M → K) (w : ℕ → Bool) :
    (uovSystem β toBits N M pk l o t).Holds (ofBits w) ↔
      ∑ k, l k * (embed β (toBits (publicMap N M pk (decode ofByte w o) k)) +
        embed β (toBits (t k))) = 0 := by
  have hbits : ∀ e ∈ (List.range (8 * N)).map (fun n => bitConstraint (Expr.wit (8 * o + n))),
      e.eval (ofBits w : ℕ → F) = 0 := by
    simp only [List.mem_map]
    rintro e ⟨n, -, rfl⟩
    exact bitConstraint_bits w _
  have hout : (evalCombinedPublicMap β toBits N M pk (fun i => byteLoad β (o + i)) l +
      Expr.const (combineVec β toBits l t)).eval (ofBits w) =
      ∑ k, l k * (embed β (toBits (publicMap N M pk (decode ofByte w o) k)) +
        embed β (toBits (t k))) := by
    simp only [Expr.eval_add, Expr.eval_const, eval_evalCombinedPublicMap_bits hι, combineVec_eq,
      mul_add, Finset.sum_add_distrib]
  rw [uovSystem, System.holds_append, ← hout]
  simp only [System.Holds, List.mem_singleton, forall_eq]
  exact ⟨fun h => h.2, fun h => ⟨hbits, h⟩⟩

/-- **Completeness.** If the witness bits encode a preimage, `P(σ) = t`, every constraint holds. -/
theorem uov_complete (hι : IsEmbedding β toBits ofByte) (N M : ℕ) (pk : ℕ → K) (l : Fin M → F)
    (o : ℕ) (t : Fin M → K) (w : ℕ → Bool) (h : publicMap N M pk (decode ofByte w o) = t) :
    (uovSystem β toBits N M pk l o t).Holds (ofBits w) := by
  rw [uov_holds_iff hι, h]
  simp [CharTwo.add_self_eq_zero]

/-- **Soundness (deterministic).** If the constraints hold at any committed values `w ∈ F^ℓ`,
then the bits of `s` are bits, and their bytes `σ` satisfy `Σ_k l_k (ι(P(σ)_k) + ι(t_k)) = 0`. -/
theorem uov_sound (hι : IsEmbedding β toBits ofByte) (N M : ℕ) (pk : ℕ → K) (l : Fin M → F)
    (o : ℕ) (t : Fin M → K) (w : ℕ → F) (h : (uovSystem β toBits N M pk l o t).Holds w) :
    ∃ wb : ℕ → Bool, (∀ n < 8 * N, w (8 * o + n) = bitF (wb (8 * o + n))) ∧
      ∑ k, l k * (embed β (toBits (publicMap N M pk (decode ofByte wb o) k)) +
        embed β (toBits (t k))) = 0 := by
  classical
  rw [uovSystem, System.holds_append] at h
  obtain ⟨hb, ho⟩ := h
  have hbit : ∀ n < 8 * N, w (8 * o + n) = bitF (decide (w (8 * o + n) = 1)) := fun n hn =>
    eq_bitF_of_bitConstraint (hb _ (List.mem_map.2 ⟨n, List.mem_range.2 hn, rfl⟩))
  refine ⟨fun i => decide (w i = 1), hbit, ?_⟩
  have hw := ho _ (List.mem_singleton_self _)
  simp only [Expr.eval_add, Expr.eval_const, eval_evalCombinedPublicMap_of_bits hι N M pk l o w
    (fun i => decide (w i = 1)) hbit, combineVec_eq] at hw
  simpa only [mul_add, Finset.sum_add_distrib] using hw

/-! ### The combination step -/

/-- If the combination vanishes for every `l`, then `P(σ) = t` (take `l = e_k`). -/
theorem publicMap_eq_of_forall (hι : IsEmbedding β toBits ofByte) {N M : ℕ} {pk : ℕ → K}
    {σ : ℕ → K} {t : Fin M → K}
    (h : ∀ l : Fin M → F, ∑ k, l k * (embed β (toBits (publicMap N M pk σ k)) +
      embed β (toBits (t k))) = 0) :
    publicMap N M pk σ = t := by
  funext k
  have := h (Pi.single k 1)
  rw [Finset.sum_eq_single k (fun k' _ hk' => by simp [hk']) (by simp)] at this
  simp only [Pi.single_eq_same, one_mul] at this
  exact hι.injective (by
    simpa using (CharTwo.add_eq_zero (R := F)).1 this)

/-- **The combination step.** If `P(σ) ≠ t`, then exactly a `1/|F|` fraction of the coefficient
vectors `l` make the combination vanish: `#bad · |F| = |F^M|`. (`σ` and `t` must be fixed before
`l` is drawn; in the protocols `l = H(chal₂ ‖ dst)`.) -/
theorem uov_card_bad [Fintype F] [DecidableEq F] (hι : IsEmbedding β toBits ofByte) {N M : ℕ}
    {pk : ℕ → K} {σ : ℕ → K} {t : Fin M → K} (h : publicMap N M pk σ ≠ t) :
    #{l : Fin M → F | ∑ k, l k * (embed β (toBits (publicMap N M pk σ k)) +
      embed β (toBits (t k))) = 0} * Fintype.card F = Fintype.card (Fin M → F) := by
  refine SeedExtraction.card_combination_eq_zero _ fun ha => h ?_
  funext k
  have := congrFun ha k
  exact hι.injective (by simpa using (CharTwo.add_eq_zero (R := F)).1 this)

theorem uov_bad_prob [Fintype F] [DecidableEq F] (hι : IsEmbedding β toBits ofByte) {N M : ℕ}
    {pk : ℕ → K} {σ : ℕ → K} {t : Fin M → K} (h : publicMap N M pk σ ≠ t) :
    (#{l : Fin M → F | ∑ k, l k * (embed β (toBits (publicMap N M pk σ k)) +
      embed β (toBits (t k))) = 0} : ℝ) / Fintype.card (Fin M → F) = (Fintype.card F : ℝ)⁻¹ := by
  refine SeedExtraction.combination_prob _ fun ha => h ?_
  funext k
  have := congrFun ha k
  exact hι.injective (by simpa using (CharTwo.add_eq_zero (R := F)).1 this)

end System

end VoleMole.Arith.UOV
