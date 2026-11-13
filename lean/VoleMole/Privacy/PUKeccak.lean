import VoleMole.Privacy.PU
import VoleMole.Spec.Moussaka
import VoleMole.Spec.Ratatouille
import VoleMole.Prob.Bytes

/-!
# (PU) for `Com`: the ideal-permutation bound at Keccak-p[800]'s sizes

`Privacy/PU.lean` bounds the (PU) advantage for a commitment `tr (π (X n r))` with `π` a uniform
permutation. Here the objects are those of the two protocols.

* `KState = Fin 100 → UInt8`: the 800-bit state; `kp800`: Keccak-p[800,12] on it
  (`Arith.Keccak.keccakP800`); `trunc a b`: the first `a` of `a + b` bytes, each value with
  `256^b` preimages (`card_fiber_trunc`).
* **Moussaka**: `XM ci cr nf r` is `encode_com_state(nf, ctx_iss, ctx_red, r)`
  (`Spec.Spec.Moussaka.comState`), injective in `r` (`XM_injective`), and
  `Com(nf, ctx_iss, ctx_red, r) = trunc 45 55 (kp800 (XM ci cr nf r))` (`com_eq_comP`): `Com` is
  `comP kp800 (XM ci cr) (trunc 45 55)`. With a uniform permutation in place of `kp800`,
  **`puAdvPerm_moussaka_le`**: `≤ (c + q)/(2¹²⁸ − q) + q/(2⁴⁴⁰ − q)`.
* **Ratatouille**: `XR ctx t nf r` is `encode_com_state(nf, ctx, t, r)`
  (`Arith.Ratatouille.comState`), `Com(nf, ctx, t, r) = trunc 32 68 (kp800 (XR ctx t nf r))`
  (`ratatouille_com_eq_comP`), and **`puAdvPerm_ratatouille_le`**:
  `≤ (c + q)/(2¹²⁸ − q) + q/(2⁵⁴⁴ − q)`.

`q` counts the predictor's forward and inverse queries to the permutation and `c` its candidates.
The bounds are for a uniformly random permutation. They say nothing about the 12-round
Keccak-p[800] itself beyond the absence of generic attacks (`Privacy/PU.lean`, last paragraph).
-/

open Finset

-- (The fibre sizes `2⁴⁴⁰`, `2⁵⁴⁴` are written as powers; nothing evaluates them.)
set_option exponentiation.threshold 600

namespace VoleMole.Privacy.PU

open VoleMole.Arith

/-! ## The state, Keccak-p[800] and truncation -/

/-- The 800-bit state as a finite type. -/
abbrev KState := Fin 100 → UInt8

/-- A state as `Arith.Keccak.State`. -/
def toSt (s : KState) : Keccak.State := Vector.ofFn s

/-- Keccak-p[800,12] on `KState`. -/
def kp800 (s : KState) : KState := fun i => (Keccak.keccakP800 (toSt s))[i]

/-- The first `a` of `a + b` entries. -/
def trunc (a b : ℕ) {α : Type} (s : Fin (a + b) → α) : Fin a → α := fun i => s (Fin.castAdd b i)

/-- **Every truncation has `|α|^b` preimages.** -/
theorem card_fiber_trunc (a b : ℕ) {α : Type} [Fintype α] [DecidableEq α] (t : Fin a → α) :
    (univ.filter fun s : Fin (a + b) → α => trunc a b s = t).card = Fintype.card α ^ b := by
  have h : (univ.filter fun s : Fin (a + b) → α => trunc a b s = t) =
      (univ : Finset (Fin b → α)).map ⟨fun u => Fin.append t u, fun u u' h => by
        funext j
        have := congrFun h (Fin.natAdd a j)
        simpa using this⟩ := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · rintro rfl
      exact ⟨fun j => s (Fin.natAdd a j), Fin.append_castAdd_natAdd⟩
    · rintro ⟨u, rfl⟩
      funext i
      exact Fin.append_left t u i
  rw [h, Finset.card_map, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]

lemma card_coins (n : ℕ) : Fintype.card (Coins n) = 2 ^ (8 * n) := by
  exact Prob.card_bytes n

/-! ## Moussaka -/

/-- **`encode_com_state(nf, ctx_iss, ctx_red, r)` as a state**, for the nullifier `n` and the
opening `r`. -/
def XM (ci cr : Spec.Bytes) (n : Coins 24) (r : Coins 16) : KState :=
  fun i => (Spec.Moussaka.comState (List.ofFn n) ci cr (List.ofFn r)).getD i.1 0

lemma toSt_XM (ci cr : Spec.Bytes) (n : Coins 24) (r : Coins 16) :
    toSt (XM ci cr n r) = Spec.stateOfBytes (Spec.Moussaka.comState (List.ofFn n) ci cr (List.ofFn r)) := rfl

/-- **`Com` is one truncated call of Keccak-p[800,12]**:
`Com(nf, ctx_iss, ctx_red, r) = trunc 45 55 (kp800 (XM ci cr nf r))`. -/
theorem com_eq_comP (ci cr : Spec.Bytes) (n : Coins 24) (r : Coins 16) :
    Spec.Moussaka.com (List.ofFn n) ci cr (List.ofFn r) =
      List.ofFn (comP kp800 (XM ci cr) (trunc 45 55) n r) := by
  unfold Spec.Moussaka.com comP
  rw [← toSt_XM]
  apply List.ext_getElem
  · rw [List.length_take, Vector.length_toList, List.length_ofFn]
    rfl
  · intro i h1 h2
    rw [List.getElem_take, Vector.getElem_toList, List.getElem_ofFn]
    rfl

/-- The opening is bytes `7 … 22` of the state. -/
lemma XM_apply_r (ci cr : Spec.Bytes) (n : Coins 24) (r : Coins 16)
    (j : Fin 16) : XM ci cr n r ⟨7 + j.1, by omega⟩ = r j := by
  have h7 : Spec.Moussaka.comDst.length = 7 := by decide
  have hj := j.2
  simp only [XM, Spec.Moussaka.comState, List.append_assoc]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [h7]; omega), h7,
    Nat.add_sub_cancel_left, List.getElem?_append_left (by rw [List.length_ofFn]; exact hj),
    List.getElem?_ofFn]
  simp only [hj, ↓reduceDIte]
  rfl

/-- **The encoding is injective in the opening.** -/
theorem XM_injective (ci cr : Spec.Bytes) (n : Coins 24) :
    Function.Injective (XM ci cr n) := by
  intro r r' h
  funext j
  rw [← XM_apply_r ci cr n r j, ← XM_apply_r ci cr n r' j, h]

/-- **(PU) for Moussaka's `Com` in the ideal-permutation model.** With a uniform permutation of
the 800-bit state in place of Keccak-p[800,12], a predictor of the 128-bit opening with at most
`q` forward and inverse queries and at most `c` candidates has advantage at most

    (c + q) / (2¹²⁸ − q) + q / (2⁴⁴⁰ − q). -/
theorem puAdvPerm_moussaka_le {Aux : Type} [Fintype Aux] [Nonempty Aux] (ci cr : Spec.Bytes)
    (A : Coins 24 → Coins 45 → Aux → PTree KState (Finset (Coins 16)))
    {q c : ℕ} (hA : ∀ n t a, (A n t a).Bound q) (hc : ∀ n t a π, ((A n t a).run π).card ≤ c)
    (hq : q < 2 ^ 128) :
    puAdvPerm (XM ci cr) (trunc 45 55) A ≤
      (c + q) / (2 ^ 128 - q : ℝ) + q / (2 ^ 440 - q : ℝ) := by
  have hR : Fintype.card (Coins 16) = 2 ^ 128 :=
    (card_coins 16).trans (by norm_num)
  have hm : ∀ t : Coins 45,
      (2 ^ 8) ^ 55 ≤ (univ.filter fun y : KState => trunc 45 55 y = t).card := by
    intro t
    rw [card_fiber_trunc 45 55 t, Prob.card_uint8]
  have := puAdvPerm_le (XM ci cr) (XM_injective ci cr) (trunc 45 55) A hA hc hm
    (by rw [hR]; exact hq) (lt_of_lt_of_le hq (by
      rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by norm_num)))
  rw [hR] at this
  have e : (((2 ^ 8) ^ 55 : ℕ) : ℝ) = 2 ^ 440 := by
    rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
  rw [e] at this
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using this

/-! ## Ratatouille -/

/-- A block as a function of the index (`0` beyond the end), as `Spec.Ratatouille.Bytes.fn`. -/
def fnOf {k : ℕ} (c : Coins k) : ℕ → UInt8 := fun i => if h : i < k then c ⟨i, h⟩ else 0

lemma fn_ofFn {k : ℕ} (c : Coins k) : Spec.Ratatouille.Bytes.fn (Vector.ofFn c) = fnOf c := by
  funext i
  unfold Spec.Ratatouille.Bytes.fn fnOf
  split_ifs with h
  · simp
  · rfl

/-- **`encode_com_state(nf, ctx, t, r)` as a state** (`Arith.Ratatouille.comState`), for the
nullifier `n` and the opening `r`. -/
def XR (ctx : ℕ → UInt8) (t : ℕ) (n : Coins 24) (r : Coins 16) : KState :=
  fun i => (Arith.Ratatouille.comState (fnOf n) ctx t (fnOf r))[i.1]

lemma toSt_XR (ctx : ℕ → UInt8) (t : ℕ) (n : Coins 24) (r : Coins 16) :
    toSt (XR ctx t n r) = Arith.Ratatouille.comState (fnOf n) ctx t (fnOf r) := by
  unfold toSt XR
  ext i hi
  simp

/-- **Ratatouille's `Com` is one truncated call of Keccak-p[800,12]**:
`Com(nf, ctx, t, r) = trunc 32 68 (kp800 (XR ctx t nf r))`. -/
theorem ratatouille_com_eq_comP (ctx : Spec.Ratatouille.Context)
    (t : Spec.Ratatouille.Credits) (n : Coins 24) (r : Coins 16) :
    Spec.Ratatouille.com (Vector.ofFn n) ctx t (Vector.ofFn r) =
      Vector.ofFn (comP kp800 (XR ctx.fn t.toNat) (trunc 32 68) n r) := by
  unfold Spec.Ratatouille.com comP
  rw [fn_ofFn, fn_ofFn]
  refine congrArg Vector.ofFn (funext fun k => ?_)
  have hk : k.1 < 100 := by omega
  unfold Arith.Ratatouille.commit Arith.Ratatouille.stateByte trunc kp800
  rw [toSt_XR]
  generalize Keccak.keccakP800 _ = v
  simp only [hk, ↓reduceDIte]
  rfl

/-- The opening is bytes `7 … 22` of the state. -/
lemma XR_apply_r (ctx : ℕ → UInt8) (t : ℕ) (n : Coins 24) (r : Coins 16) (j : Fin 16) :
    XR ctx t n r ⟨7 + j.1, by omega⟩ = r j := by
  have hj := j.2
  simp only [XR, Arith.Ratatouille.comState, Vector.getElem_ofFn, fnOf,
    show ¬ (7 + j.1 < 7) from by omega, show 7 + j.1 < 23 from by omega,
    show 7 + j.1 - 7 < 16 from by omega, ↓reduceIte, ↓reduceDIte]
  exact congrArg r (Fin.ext (Nat.add_sub_cancel_left ..))

theorem XR_injective (ctx : ℕ → UInt8) (t : ℕ) (n : Coins 24) : Function.Injective (XR ctx t n) := by
  intro r r' h
  funext j
  rw [← XR_apply_r ctx t n r j, ← XR_apply_r ctx t n r' j, h]

/-- **(PU) for Ratatouille's `Com` in the ideal-permutation model**: at most

    (c + q) / (2¹²⁸ − q) + q / (2⁵⁴⁴ − q)

for a predictor with at most `q` forward and inverse queries and at most `c` candidates. -/
theorem puAdvPerm_ratatouille_le {Aux : Type} [Fintype Aux] [Nonempty Aux] (ctx : ℕ → UInt8)
    (t : ℕ) (A : Coins 24 → Coins 32 → Aux → PTree KState (Finset (Coins 16)))
    {q c : ℕ} (hA : ∀ n t a, (A n t a).Bound q) (hc : ∀ n t a π, ((A n t a).run π).card ≤ c)
    (hq : q < 2 ^ 128) :
    puAdvPerm (XR ctx t) (trunc 32 68) A ≤
      (c + q) / (2 ^ 128 - q : ℝ) + q / (2 ^ 544 - q : ℝ) := by
  have hR : Fintype.card (Coins 16) = 2 ^ 128 :=
    (card_coins 16).trans (by norm_num)
  have hm : ∀ t : Coins 32,
      (2 ^ 8) ^ 68 ≤ (univ.filter fun y : KState => trunc 32 68 y = t).card := by
    intro t
    rw [card_fiber_trunc 32 68 t, Prob.card_uint8]
  have := puAdvPerm_le (XR ctx t) (XR_injective ctx t) (trunc 32 68) A hA hc hm
    (by rw [hR]; exact hq) (lt_of_lt_of_le hq (by
      rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by norm_num)))
  rw [hR] at this
  have e : (((2 ^ 8) ^ 68 : ℕ) : ℝ) = 2 ^ 544 := by
    rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
  rw [e] at this
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using this

end VoleMole.Privacy.PU
