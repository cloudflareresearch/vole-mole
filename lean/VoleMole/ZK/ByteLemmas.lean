import VoleMole.ZK.Sim
import VoleMole.Prob.Bytes
import VoleMole.Verifier.Bridge.Prover

/-!
# Byte and word bookkeeping for the ideal-tape prover

Small facts about `ByteArray`, little-endian words and the tape blocks of `ZK/Sim.lean`, used by
`ZK/IdealFields.lean` and `ZK/TapeOf.lean`: what `Sim.ba`, `Sim.blk`, `++`, `wordsOf`,
`bytesOfWords` and `xorWords` read back.
-/

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith

@[simp] lemma size_ba {n : ℕ} (b : Bytes n) : (ba b).size = n := by
  simp [ba, ByteArray.size]

lemma get!_ba {n : ℕ} (b : Bytes n) {i : ℕ} (hi : i < n) : (ba b).get! i = b ⟨i, hi⟩ := by
  simp [ba, ByteArray.get!, hi]

lemma get!_ba_of_le {n : ℕ} (b : Bytes n) {i : ℕ} (hi : n ≤ i) : (ba b).get! i = 0 := by
  rw [byteArray_get!_eq]
  simp [ba, show ¬ i < n by omega]
  rfl

lemma ba_eq_prob {n : ℕ} (b : Bytes n) : ba b = Prob.Bytes.ba b := rfl

/-- Two byte strings of the same size with the same bytes are equal. -/
lemma byteArray_ext_get! {a b : ByteArray} (hs : a.size = b.size)
    (h : ∀ k < a.size, a.get! k = b.get! k) : a = b := by
  apply ByteArray.ext
  apply Array.ext hs
  intro k h1 h2
  have := h k h1
  rw [byteArray_get!_eq, byteArray_get!_eq] at this
  simpa [Array.getElem?_eq_getElem h1, Array.getElem?_eq_getElem h2] using this

lemma get!_append (a b : ByteArray) (k : ℕ) :
    (a ++ b).get! k = if k < a.size then a.get! k else b.get! (k - a.size) := by
  rw [byteArray_get!_eq, byteArray_get!_eq, byteArray_get!_eq, ByteArray.data_append,
    Array.getElem?_append]
  have : a.size = a.data.size := rfl
  rw [this]
  split_ifs <;> rfl

lemma get!_of_le {x : ByteArray} {k : ℕ} (h : x.size ≤ k) : x.get! k = 0 := by
  rw [byteArray_get!_eq, Array.getElem?_eq_none (by exact h)]
  rfl

lemma get!_zeros (m k : ℕ) : (Prover.zeros m).get! k = 0 := by
  rw [byteArray_get!_eq]
  simp only [Prover.zeros, Array.getElem?_replicate]
  split_ifs <;> rfl

lemma get!_extract0 (x : ByteArray) {n k : ℕ} (hk : k < n) (hn : n ≤ x.size) :
    (x.extract 0 n).get! k = x.get! k := by
  rw [byteArray_get!_eq, byteArray_get!_eq, ByteArray.data_extract, Array.getElem?_extract]
  have : k < x.size := by omega
  simp [hk, this]

/-- `blk n b` reads the first `n` bytes back. -/
lemma get_blk (n : ℕ) (b : ByteArray) (i : Fin n) : blk n b i = b.get! i := rfl

/-- `ba ∘ blk` is `Prover.fit`. -/
lemma ba_blk (n : ℕ) (b : ByteArray) : ba (blk n b) = Prover.fit b n := by
  apply byteArray_ext_get!
  · rw [size_ba, fit_size]
  intro k hk
  rw [size_ba] at hk
  rw [get!_ba _ hk, get_blk, Prover.fit, get!_extract0 _ hk (by
    rw [ByteArray.size_append, zeros_size]; omega), get!_append]
  show b.get! k = _
  split_ifs with h
  · rfl
  · rw [get!_zeros, get!_of_le (by omega)]

lemma ba_blk_of_size {n : ℕ} {b : ByteArray} (h : b.size = n) : ba (blk n b) = b := by
  rw [ba_blk, fit_of_size h]

/-! ## Words -/

/-- Byte `k` of `bytesOfWords (wordsOf b)` is `b[k]` (if `8 ∣ |b|`). -/
lemma bytesOfWords_wordsOf {b : ByteArray} (hb : b.size % 8 = 0) : bytesOfWords (wordsOf b) = b := by
  have hws : (wordsOf b).size = b.size / 8 := by simp [wordsOf]
  apply byteArray_ext_get!
  · rw [bytesOfWords_size, hws]; omega
  intro k hk
  rw [bytesOfWords_size, hws] at hk
  rw [bytesOfWords_get _ (by rw [hws]; omega), wordsOf, getElem!_range_map _ _ (by omega),
    Prob.word_byte _ _ (Nat.mod_lt _ (by norm_num))]
  congr 1
  omega

lemma toUInt8_shiftRight_xor (a b : UInt64) (s : UInt64) :
    ((a ^^^ b) >>> s).toUInt8 = (a >>> s).toUInt8 ^^^ (b >>> s).toUInt8 := by
  apply UInt8.toNat_inj.1
  rw [UInt8.toNat_xor, UInt64.toNat_toUInt8, UInt64.toNat_toUInt8, UInt64.toNat_toUInt8,
    UInt64.toNat_shiftRight, UInt64.toNat_shiftRight, UInt64.toNat_shiftRight, UInt64.toNat_xor]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_shiftRight]
  by_cases hi : i < 8 <;> simp [hi]

/-- Byte `k` of the XOR of two word arrays (of the same length). -/
lemma bytesOfWords_xorWords_get (a b : Array UInt64) (hab : a.size = b.size) {k : ℕ}
    (hk : k < 8 * a.size) :
    (bytesOfWords (xorWords a b)).get! k = (bytesOfWords a).get! k ^^^ (bytesOfWords b).get! k := by
  have hq : k / 8 < a.size := by omega
  rw [bytesOfWords_get _ (by rw [xorWords_size]; exact hk), bytesOfWords_get _ hk,
    bytesOfWords_get _ (by rw [← hab]; exact hk), xorWords_get _ _ hq, ← toUInt8_shiftRight_xor]

/-! ## Concatenations -/

lemma size_foldl_append' {α : Type*} (f : α → ByteArray) : ∀ (l : List α) (acc : ByteArray),
    (l.foldl (fun acc i => acc ++ f i) acc).size = acc.size + (l.map fun i => (f i).size).sum
  | [], _ => by simp
  | i :: l, acc => by
    rw [List.foldl_cons, size_foldl_append' f l, ByteArray.size_append]
    simp [Nat.add_assoc]

/-- Byte `j` of a concatenation of blocks of `m` bytes is byte `j % m` of block `j / m`. -/
lemma get!_foldl_blocks (f : ℕ → ByteArray) (m : ℕ) (hf : ∀ i, (f i).size = m) :
    ∀ (n : ℕ) (j : ℕ), j < n * m →
      ((List.range n).foldl (fun acc i => acc ++ f i) ByteArray.empty).get! j =
        (f (j / m)).get! (j % m)
  | 0, j, hj => by simp at hj
  | n + 1, j, hj => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, get!_append]
    have hsz : ((List.range n).foldl (fun acc i => acc ++ f i) ByteArray.empty).size = n * m := by
      rw [size_foldl_append']; simp [hf, List.sum_replicate]
    rw [hsz]
    split_ifs with h
    · exact get!_foldl_blocks f m hf n j h
    · have hm : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · subst h0; simp at hj
        · exact h0
      have e1 : j / m = n := by
        apply Nat.div_eq_of_lt_le <;> nlinarith
      have e2 : j % m = j - n * m := by
        rw [Nat.mod_eq_sub_mul_div, e1, Nat.mul_comm]
      rw [e1, e2]

end VoleMole.ZK.Sim
