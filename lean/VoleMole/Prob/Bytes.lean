import VoleMole.Prob.Uniform
import VoleMole.Verifier.Bridge.Chain

/-!
# Uniform bytes and the executable verifier's challenge decodings

The random oracle answers `chal1` (136 bytes), `chal2` (56 bytes) and `chal3` (16 bytes) are byte
strings; the extraction theorems use them decoded (`Bridge/KOS.lean`'s `chOf`, the `zkCoeff`
arguments of `Bridge/Chain.lean`, `blocksOf ∘ BAVC.deltaBit`). This file proves that each decoding
is a bijection, so a uniform byte string decodes to a uniform challenge (`prU_map_equiv`). No set of
size `2⁶⁴` or more is enumerated: every cardinality is a product of `|UInt8| = 2⁸` and `|GF128|`.

* `Bytes n`: `n` bytes as a finite type, `Bytes.ba` the `ByteArray`; `card_bytes`.
* `word_byte`: byte `j` of the little-endian word `W128.word b off` is `b[off + j]`, so the words
  at offsets `0, 8, 16, …` determine the bytes (`eq_of_words`).
* `gf128OfBytesEquiv : Bytes 16 ≃ GF128` (`gfOfBytes`).
* `card_shortKeys : #shortKeys = 2⁶⁴` (by injectivity of `Nat.toUInt64` below `2⁶⁴`).
* `chal1Equiv : Bytes 136 ≃ Seed.Ch GF128 shortKeys`, forward map `chOf gfId mem_shortKeys` (eight
  field elements and the low word at byte 128).
* `chal2Equiv : Bytes 56 ≃ Chal2 = GF128 × GF128 × GF128 × shortKeys`, the arguments
  `gfOfBytes chal2 0/16/32`, `⟨W128.word chal2 48, 0⟩` that `*_extract_chain` passes to `zkCoeff`.
* `combEquiv M : Bytes (16·M) ≃ (Fin M → GF128)` (`combDec`, as `combinationOf` decodes `l`).
* **`hδ`, deterministic** (L1 bookkeeping): `admissible` (the `2¹²⁰` values of `chal3` with zero
  grinding bits, those `check_format` accepts), `deltaBlocks x = blocksOf (deltaBit x)`,
  `deltaBlocks_injOn`, and `prU_accept_le`: if at most `N` admissible `chal3` are accepted, a
  uniform `chal3` is accepted with probability `≤ N/2¹²⁸`.
-/

open Finset

namespace VoleMole.Prob

open VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge

/-- `n` bytes, as a finite type. -/
abbrev Bytes (n : ℕ) := Fin n → UInt8

/-- The byte string of `b`. -/
def Bytes.ba {n : ℕ} (b : Bytes n) : ByteArray := ⟨Array.ofFn b⟩

@[simp] lemma Bytes.size_ba {n : ℕ} (b : Bytes n) : b.ba.size = n := by
  simp [Bytes.ba, ByteArray.size]

lemma Bytes.get!_ba {n : ℕ} (b : Bytes n) {i : ℕ} (hi : i < n) : b.ba.get! i = b ⟨i, hi⟩ := by
  simp [Bytes.ba, ByteArray.get!, hi]

theorem card_uint8 : Fintype.card UInt8 = 2 ^ 8 := by
  rw [← FinEnum.card_eq_fintypeCard]; rfl

theorem card_bytes (n : ℕ) : Fintype.card (Bytes n) = 2 ^ (8 * n) := by
  rw [Fintype.card_fun, card_uint8, Fintype.card_fin, ← pow_mul]

/-! ## Bytes of a word -/

/-- The little-endian word of the bytes `x 0, …, x 7`. -/
def pack8 (x : ℕ → UInt8) : UInt64 :=
  (List.range 8).foldl (fun w j => w ||| ((x j).toUInt64 <<< (8 * j).toUInt64)) 0

lemma word_eq_pack8 (b : ByteArray) (off : ℕ) :
    W128.word b off = pack8 fun j => b.get! (off + j) := by
  simp only [W128.word, Id.run, bind_pure]
  rw [forIn_range_foldl 8 0 _ (fun j w => w ||| ((b.get! (off + j)).toUInt64 <<< (8 * j).toUInt64))
    (fun _ _ => rfl)]
  rfl

lemma pack8_byte (x : ℕ → UInt8) {j : ℕ} (hj : j < 8) :
    ((pack8 x) >>> (8 * j).toUInt64).toUInt8 = x j := by
  apply UInt8.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases j <;>
    simp (disch := omega) [pack8, List.range_succ, decide_eq_true, decide_eq_false]

/-- **Byte `j` of `W128.word b off` is `b[off + j]`.** -/
theorem word_byte (b : ByteArray) (off : ℕ) {j : ℕ} (hj : j < 8) :
    ((W128.word b off) >>> (8 * j).toUInt64).toUInt8 = b.get! (off + j) := by
  rw [word_eq_pack8, pack8_byte _ hj]

/-- **The words at offsets `0, 8, 16, …` determine the bytes.** -/
theorem eq_of_words {n : ℕ} (hn : n % 8 = 0) {b b' : Bytes n}
    (h : ∀ o, 8 * o < n → W128.word b.ba (8 * o) = W128.word b'.ba (8 * o)) : b = b' := by
  funext ⟨k, hk⟩
  have hk8 : 8 * (k / 8) < n := by omega
  have hj : k % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have e := congrArg (fun w : UInt64 => (w >>> (8 * (k % 8)).toUInt64).toUInt8) (h _ hk8)
  simp only [word_byte _ _ hj, Nat.div_add_mod] at e
  rwa [Bytes.get!_ba _ hk, Bytes.get!_ba _ hk] at e

lemma words_of_gf_eq {b b' : ByteArray} {off : ℕ} (h : gfOfBytes b off = gfOfBytes b' off) :
    ∀ o, (8 * o = off ∨ 8 * o = off + 8) → W128.word b (8 * o) = W128.word b' (8 * o) := by
  rintro o (e | e) <;> rw [e]
  · exact congrArg GF128.lo h
  · exact congrArg GF128.hi h

/-! ## `GF128` from 16 bytes -/

/-- `gfOfBytes` on 16 bytes. -/
def gfDec (b : Bytes 16) : GF128 := gfOfBytes b.ba 0

theorem gfDec_injective : Function.Injective gfDec := fun b b' h =>
  eq_of_words (by norm_num) fun o ho => words_of_gf_eq h o (by omega)

/-- **A uniform 16-byte string is a uniform field element.** -/
noncomputable def gf128OfBytesEquiv : Bytes 16 ≃ GF128 :=
  Equiv.ofBijective gfDec ((Fintype.bijective_iff_injective_and_card _).2
    ⟨gfDec_injective, by rw [card_bytes, GF128.card_eq]⟩)

@[simp] lemma gf128OfBytesEquiv_apply (b : Bytes 16) : gf128OfBytesEquiv b = gfOfBytes b.ba 0 :=
  rfl

/-! ## The short keys -/

/-- **`2⁶⁴` short keys**, without enumerating them. -/
theorem card_shortKeys : #shortKeys = 2 ^ 64 := by
  rw [shortKeys, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb e
  simp only [coe_range, Set.mem_Iio] at ha hb
  have := congrArg (fun x : GF128 => x.lo.toNat) e
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat'] at this
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

/-! ## `chal1` -/

theorem card_ch : Fintype.card (Seed.Ch GF128 shortKeys) = 2 ^ (8 * 136) := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, GF128.card_eq,
    Fintype.card_coe, card_shortKeys, ← pow_mul, ← pow_add]

/-- `chal1` decoded as a VOLEHash challenge (`Chain.kosCh`). -/
noncomputable def ch1Dec (b : Bytes 136) : Seed.Ch GF128 shortKeys := chOf gfId mem_shortKeys b.ba

theorem ch1Dec_injective : Function.Injective ch1Dec := by
  intro b b' h
  simp only [ch1Dec, chOf, gfId_apply, Prod.mk.injEq, Subtype.mk.injEq] at h
  obtain ⟨hr, hs, ht⟩ := h
  refine eq_of_words (by norm_num) fun o ho => ?_
  rcases (by omega : o < 8 ∨ (8 ≤ o ∧ o < 16) ∨ o = 16) with h8 | ⟨h8, h16⟩ | rfl
  · exact words_of_gf_eq (congrFun hr ⟨o / 2, by omega⟩) o (by simp only; omega)
  · exact words_of_gf_eq (congrFun hs ⟨(o - 8) / 2, by omega⟩) o (by simp only; omega)
  · exact congrArg GF128.lo ht

/-- **A uniform 136-byte `chal1` is a uniform VOLEHash challenge.** -/
noncomputable def chal1Equiv : Bytes 136 ≃ Seed.Ch GF128 shortKeys :=
  Equiv.ofBijective ch1Dec ((Fintype.bijective_iff_injective_and_card _).2
    ⟨ch1Dec_injective, by rw [card_bytes, card_ch]⟩)

@[simp] lemma chal1Equiv_apply (b : Bytes 136) : chal1Equiv b = chOf gfId mem_shortKeys b.ba := rfl

/-! ## `chal2` -/

/-- The ZKHash challenge `(r₀, r₁, s, t)`, `t` a short key. -/
abbrev Chal2 := GF128 × GF128 × GF128 × shortKeys

/-- `chal2` decoded as the `zkCoeff` arguments of `*_extract_chain`. -/
def ch2Dec (b : Bytes 56) : Chal2 :=
  (gfOfBytes b.ba 0, gfOfBytes b.ba 16, gfOfBytes b.ba 32,
    ⟨⟨W128.word b.ba 48, 0⟩, mem_shortKeys _⟩)

theorem ch2Dec_injective : Function.Injective ch2Dec := by
  intro b b' h
  simp only [ch2Dec, Prod.mk.injEq] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine eq_of_words (by norm_num) fun o ho => ?_
  rcases (by omega : o < 2 ∨ (2 ≤ o ∧ o < 4) ∨ (4 ≤ o ∧ o < 6) ∨ o = 6) with
    h' | ⟨h', h''⟩ | ⟨h', h''⟩ | rfl
  · exact words_of_gf_eq h0 o (by omega)
  · exact words_of_gf_eq h1 o (by omega)
  · exact words_of_gf_eq h2 o (by omega)
  · exact congrArg (fun t : shortKeys => (t : GF128).lo) h3

theorem card_chal2 : Fintype.card Chal2 = 2 ^ (8 * 56) := by
  simp only [Fintype.card_prod, GF128.card_eq, Fintype.card_coe, card_shortKeys, ← pow_add]

/-- **A uniform 56-byte `chal2` is a uniform ZKHash challenge.** -/
noncomputable def chal2Equiv : Bytes 56 ≃ Chal2 :=
  Equiv.ofBijective ch2Dec ((Fintype.bijective_iff_injective_and_card _).2
    ⟨ch2Dec_injective, by rw [card_bytes, card_chal2]⟩)

@[simp] lemma chal2Equiv_apply (b : Bytes 56) : chal2Equiv b = ch2Dec b := rfl

/-! ## The UOV combination `l` -/

/-- `16·M` bytes decoded as `M` field elements, as `combinationOf` decodes `H_comb(chal2 ‖ dst)`
(`gfOfBytes` at offsets `0, 16, 32, …`). -/
def combDec {M : ℕ} (b : Bytes (16 * M)) : Fin M → GF128 := fun k => gfOfBytes b.ba (16 * k)

theorem combDec_injective {M : ℕ} : Function.Injective (combDec (M := M)) := fun b b' h =>
  eq_of_words (by omega) fun o ho =>
    words_of_gf_eq (congrFun h ⟨o / 2, by omega⟩) o (by simp only; omega)

/-- **A uniform `16·M`-byte string is a uniform combination vector.** -/
noncomputable def combEquiv (M : ℕ) : Bytes (16 * M) ≃ (Fin M → GF128) :=
  Equiv.ofBijective combDec ((Fintype.bijective_iff_injective_and_card _).2
    ⟨combDec_injective, by
      rw [card_bytes, Fintype.card_fun, Fintype.card_fin, GF128.card_eq, ← pow_mul]; ring_nf⟩)

@[simp] lemma combEquiv_apply {M : ℕ} (b : Bytes (16 * M)) : combEquiv M b = combDec b := rfl

/-! ## `chal3`: admissible values and their blocks (`hδ`) -/

/-- The admissible `chal3`: the 8 grinding bits (byte 15) are zero (`Proof.checkFormat`). -/
def admissible : Finset (Bytes 16) := {x | x (Fin.last 15) = 0}

theorem card_admissible : #admissible = 2 ^ 120 := by
  have : admissible = Fintype.piFinset fun k : Fin 16 => if k = Fin.last 15 then {0} else univ := by
    ext x
    simp only [admissible, mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    refine ⟨fun h k => ?_, fun h => by simpa using h (Fin.last 15)⟩
    split_ifs with hk
    · subst hk; simpa using h
    · exact mem_univ _
  rw [this, Fintype.card_piFinset, Fin.prod_univ_castSucc]
  simp only [Fin.castSucc_ne_last, ↓reduceIte, card_singleton, mul_one, card_univ, card_uint8,
    prod_const, Fintype.card_fin, ← pow_mul]

/-- The challenge blocks of `chal3 = x` (as the verifier reads them, `onChain_of_accept`). -/
def deltaBlocks (x : Bytes 16) : Blocks := blocksOf (BAVC.deltaBit x.ba)

lemma and_one_eq (a : UInt8) {i : ℕ} (hi : i < 8) :
    (a >>> i.toUInt8) &&& 1 = if a.toBitVec.getLsbD i then 1 else 0 := by
  apply UInt8.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  interval_cases i <;> split_ifs with h <;> interval_cases j <;> simp_all

lemma bit_eq_getLsbD (a : UInt8) {i : ℕ} (hi : i < 8) :
    ((a >>> i.toUInt8) &&& 1 == 1) = a.toBitVec.getLsbD i := by
  rw [and_one_eq a hi]; split_ifs with h <;> simp [h]

lemma uint8_ext_bits {a b : UInt8}
    (h : ∀ i < 8, ((a >>> i.toUInt8) &&& 1 == 1) = ((b >>> i.toUInt8) &&& 1 == 1)) : a = b := by
  apply UInt8.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [← bit_eq_getLsbD a hi, ← bit_eq_getLsbD b hi, h i hi]

set_option maxRecDepth 4000 in
/-- **`hδ`: admissible `chal3` decode injectively into blocks.** The blocks are bits `0 … 119`;
bits `120 … 127` are zero. -/
theorem deltaBlocks_injOn : Set.InjOn deltaBlocks (admissible : Set (Bytes 16)) := by
  intro x hx x' hx' h
  simp only [admissible, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx hx'
  funext k
  by_cases hk : k = Fin.last 15
  · rw [hk, hx, hx']
  have hk15 : (k : ℕ) < 15 := by
    have := k.isLt
    have : (k : ℕ) ≠ 15 := fun e => hk (Fin.ext e)
    omega
  refine uint8_ext_bits fun i hi => ?_
  have hc : 8 * k + i < 120 := by omega
  have e := congrArg (fun Δ => dbitOf Δ (8 * k + i)) h
  simp only [deltaBlocks, dbitOf_blocksOf _ hc, BAVC.deltaBit, hc, decide_true,
    Bool.true_and] at e
  have h8 : (8 * (k : ℕ) + i) / 8 = k := by omega
  have h8' : (8 * (k : ℕ) + i) % 8 = i := by omega
  rwa [h8, h8', Bytes.get!_ba _ k.isLt, Bytes.get!_ba _ k.isLt] at e

/-- **The final step of the assembly**: if at most `N` admissible `chal3` are accepted, a uniform
`chal3` is admissible and accepted with probability `≤ N / 2¹²⁸`. -/
theorem prU_accept_le (acc : Bytes 16 → Prop) [DecidablePred acc] {N : ℕ}
    (h : #{x ∈ admissible | acc x} ≤ N) :
    prU (Bytes 16) (fun x => x ∈ admissible ∧ acc x) ≤ (N : ENNReal) / 2 ^ 128 := by
  refine (prU_le_of_card_le _ (le_trans (le_of_eq ?_) h)).trans_eq ?_
  · simp only [admissible, Finset.filter_filter, Finset.mem_filter, Finset.mem_univ, true_and]
  · simp only [card_bytes, Nat.cast_pow, Nat.cast_ofNat, Nat.reduceMul]

end VoleMole.Prob
