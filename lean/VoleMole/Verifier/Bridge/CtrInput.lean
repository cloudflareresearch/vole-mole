import VoleMole.Verifier.VOLE
import VoleMole.Seed.Commitments

/-!
# Bridge: the executable AES-CTR inputs are `Seed.Commitments.ctrInput`

`Seed/Commitments.lean` models the input block of `aes_ctr_prg` as four 32-bit lanes,
`ctrInput iv c t = iv ⊞ (c, 0, 0, t)`, and proves that inputs of the four AES roles (GGM nodes,
leaf commitments, mask top bits, ConvertToVOLE) are pairwise distinct under one `iv`. The
executable PRG (`Verifier/AES.lean`) builds the block as bytes (`ctrBlock`). This file connects the
two:

* `lanes_ctrBlock`: reading `ctrBlock iv c t` as four little-endian lanes gives
  `ctrInput (lanes iv) c t`, for any 16-byte `iv` and 32-bit `c`, `t`;
* `prgExpanded_eq`: block `j` of `prg key iv t c n` is the AES encryption of `ctrBlock iv (c + j) t`;
* `children_tweak`, `leafCom_tweak`, `vole_tweak`: the tweaks the executable verifier uses for
  GGM node `n`, the leaf commitments of vector `i` and ConvertToVOLE of vector `i` lie in the tweak
  ranges `Commitments.tweaks` of their roles;
* `ctrBlock_ne_of_roles`: hence two `ctrBlock`s of different roles under the same `iv` are
  different byte strings, whatever their counters (`Commitments.role_inputs_ne`).

Nothing is assumed here: these are statements about the executable definitions.
-/

namespace VoleMole.Verifier.Bridge

open VoleMole.Verifier VoleMole.Verifier.AES VoleMole.Seed.Commitments

/-- A 16-byte block as four little-endian 32-bit lanes. -/
def lanes (b : ByteArray) : Block := ![(getLE32 b 0).toNat, (getLE32 b 4).toNat,
  (getLE32 b 8).toNat, (getLE32 b 12).toNat]

lemma get!_push (b : ByteArray) (v : UInt8) (i : ℕ) :
    (b.push v).get! i = if i < b.size then b.get! i else if i = b.size then v else default := by
  simp only [ByteArray.get!, ByteArray.push, ByteArray.size, Array.getElem!_eq_getD,
    Array.getD_eq_getD_getElem?, Array.getElem?_push]
  split_ifs with h1 h2 h2 <;> first | omega | simp_all

lemma size_pushLE32 (b : ByteArray) (x : UInt32) : (pushLE32 b x).size = b.size + 4 := by
  simp only [pushLE32, ByteArray.size_push]

lemma get!_pushLE32 (b : ByteArray) (x : UInt32) (i : ℕ) :
    (pushLE32 b x).get! i = if i < b.size then b.get! i
      else if i = b.size then x.toUInt8 else if i = b.size + 1 then (x >>> 8).toUInt8
      else if i = b.size + 2 then (x >>> 16).toUInt8
      else if i = b.size + 3 then (x >>> 24).toUInt8 else default := by
  simp only [pushLE32, get!_push, ByteArray.size_push]
  split_ifs <;> first | rfl | omega

lemma toNat_shl (b : UInt8) (s : UInt32) (hk : s.toNat ≤ 24) :
    (b.toUInt32 <<< s).toNat = 2 ^ s.toNat * b.toNat := by
  have hb := b.toNat_lt
  rw [UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show s.toNat < 32 by omega)]
  rw [Nat.mod_eq_of_lt (by
    calc b.toNat * 2 ^ s.toNat < 256 * 2 ^ s.toNat :=
          Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos _)
      _ ≤ 256 * 2 ^ 24 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hk)
      _ = 2 ^ 32 := by norm_num), Nat.mul_comm]

/-- The little-endian word of four bytes, as a number. -/
lemma toNat_le32 (b0 b1 b2 b3 : UInt8) :
    (b0.toUInt32 ||| b1.toUInt32 <<< 8 ||| b2.toUInt32 <<< 16 ||| b3.toUInt32 <<< 24).toNat =
      b0.toNat + 2 ^ 8 * b1.toNat + 2 ^ 16 * b2.toNat + 2 ^ 24 * b3.toNat := by
  have h0 := b0.toNat_lt
  have h1 := b1.toNat_lt
  have h2 := b2.toNat_lt
  simp only [UInt32.toNat_or, UInt8.toNat_toUInt32,
    toNat_shl _ _ (by decide : (8 : UInt32).toNat ≤ 24),
    toNat_shl _ _ (by decide : (16 : UInt32).toNat ≤ 24),
    toNat_shl _ _ (by decide : (24 : UInt32).toNat ≤ 24), UInt32.reduceToNat]
  rw [Nat.or_comm b0.toNat, ← Nat.two_pow_add_eq_or_of_lt (by omega),
    Nat.or_comm (2 ^ 8 * b1.toNat + b0.toNat), ← Nat.two_pow_add_eq_or_of_lt (by omega),
    Nat.or_comm (2 ^ 16 * b2.toNat + (2 ^ 8 * b1.toNat + b0.toNat)),
    ← Nat.two_pow_add_eq_or_of_lt (by omega)]
  omega

lemma getLE32_pushLE32 (b : ByteArray) (x : UInt32) :
    getLE32 (pushLE32 b x) b.size = x := by
  simp only [getLE32, get!_pushLE32]
  simp only [lt_irrefl, ite_false, ite_true, show ¬b.size + 1 < b.size by omega,
    show ¬b.size + 2 < b.size by omega, show ¬b.size + 3 < b.size by omega,
    show b.size + 1 ≠ b.size by omega, show b.size + 2 ≠ b.size by omega,
    show b.size + 2 ≠ b.size + 1 by omega, show b.size + 3 ≠ b.size by omega,
    show b.size + 3 ≠ b.size + 1 by omega, show b.size + 3 ≠ b.size + 2 by omega]
  apply UInt32.toNat_inj.1
  rw [toNat_le32]
  simp only [UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, UInt32.reduceToNat,
    Nat.shiftRight_eq_div_pow, Nat.reduceMod, Nat.reducePow]
  have := x.toNat_lt
  omega

lemma getLE32_pushLE32_of_lt (b : ByteArray) (x : UInt32) (o : ℕ) (ho : o + 4 ≤ b.size) :
    getLE32 (pushLE32 b x) o = getLE32 b o := by
  simp only [getLE32, get!_pushLE32, show o < b.size by omega, show o + 1 < b.size by omega,
    show o + 2 < b.size by omega, show o + 3 < b.size by omega, ite_true]

/-- **The executable CTR block is `ctrInput`.** -/
theorem lanes_ctrBlock (iv : ByteArray) (c t : UInt32) :
    lanes (ctrBlock iv c t) = ctrInput (lanes iv) c.toNat t.toNat := by
  have s0 : (pushLE32 ByteArray.empty (getLE32 iv 0 + c)).size = 4 := by
    simp [size_pushLE32]
  set b0 := pushLE32 ByteArray.empty (getLE32 iv 0 + c)
  set b1 := pushLE32 b0 (getLE32 iv 4)
  have s1 : b1.size = 8 := by simp [b1, size_pushLE32, s0]
  set b2 := pushLE32 b1 (getLE32 iv 8)
  have s2 : b2.size = 12 := by simp [b2, size_pushLE32, s1]
  have e0 : getLE32 b0 0 = getLE32 iv 0 + c := by
    simpa using getLE32_pushLE32 ByteArray.empty (getLE32 iv 0 + c)
  have e1 : getLE32 b1 4 = getLE32 iv 4 := by rw [← s0]; exact getLE32_pushLE32 _ _
  have e2 : getLE32 b2 8 = getLE32 iv 8 := by rw [← s1]; exact getLE32_pushLE32 _ _
  have e3 : getLE32 (pushLE32 b2 (getLE32 iv 12 + t)) 12 = getLE32 iv 12 + t := by
    rw [← s2]; exact getLE32_pushLE32 _ _
  have r0 : getLE32 (pushLE32 b2 (getLE32 iv 12 + t)) 0 = getLE32 iv 0 + c := by
    rw [getLE32_pushLE32_of_lt _ _ _ (by omega), getLE32_pushLE32_of_lt _ _ _ (by omega),
      getLE32_pushLE32_of_lt _ _ _ (by omega), e0]
  have r1 : getLE32 (pushLE32 b2 (getLE32 iv 12 + t)) 4 = getLE32 iv 4 := by
    rw [getLE32_pushLE32_of_lt _ _ _ (by omega), getLE32_pushLE32_of_lt _ _ _ (by omega), e1]
  have r2 : getLE32 (pushLE32 b2 (getLE32 iv 12 + t)) 8 = getLE32 iv 8 := by
    rw [getLE32_pushLE32_of_lt _ _ _ (by omega), e2]
  simp only [ctrBlock, lanes, ctrInput]
  rw [r0, r1, r2, e3]
  funext i
  fin_cases i <;> simp

/-- Different `(counter, tweak)` pairs give different CTR blocks under the same `iv`. -/
theorem ctrBlock_inj (iv : ByteArray) {c t c' t' : UInt32}
    (h : ctrBlock iv c t = ctrBlock iv c' t') : c = c' ∧ t = t' := by
  have := congrArg lanes h
  rw [lanes_ctrBlock, lanes_ctrBlock] at this
  obtain ⟨hc, ht⟩ := ctrInput_inj _ c.toNat_lt t.toNat_lt c'.toNat_lt t'.toNat_lt this
  exact ⟨UInt32.toNat_inj.1 hc, UInt32.toNat_inj.1 ht⟩

/-- `prgExpanded` (hence `prg`) concatenates the encryptions of `ctrBlock iv (c + j) t`, `j < n`. -/
theorem prgExpanded_eq (rk iv : ByteArray) (t c : UInt32) (n : ℕ) :
    prgExpanded rk iv t c n = (List.range n).foldl
      (fun out j => out ++ encrypt rk (ctrBlock iv (c + j.toUInt32) t))
      (ByteArray.emptyWithCapacity (16 * n)) := by
  simp [prgExpanded, Std.Legacy.Range.forIn_eq_forIn_range', List.range_eq_range', Std.Legacy.Range.size]

/-! ## The executable verifier's tweaks lie in the role ranges -/

lemma toNat_toUInt32 {n : ℕ} (h : n < 2 ^ 32) : n.toUInt32.toNat = n := by
  simp only [Nat.toUInt32, UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt h

lemma numLeaves_eq : BAVC.numLeaves = L := by decide

/-- GGM node `n` (`BAVC.children`, `n < L − 1`) uses tweak `n`, in the GGM range. -/
theorem children_tweak (iv node : ByteArray) {n : ℕ} (hn : n < BAVC.numLeaves - 1) :
    BAVC.children iv node n = prg node iv n.toUInt32 0 2 ∧
      n.toUInt32.toNat ∈ tweaks .ggm := by
  refine ⟨rfl, ?_⟩
  rw [numLeaves_eq] at hn
  rw [toNat_toUInt32 (by simp [L] at hn ⊢; omega)]
  simp [tweaks]; omega

/-- The leaf commitments of vector `i < τ` (`BAVC.leafCom`) use tweak `i + L − 1`, in the leaf
range. -/
theorem leafCom_tweak (iv key : ByteArray) {i : ℕ} (hi : i < BAVC.tau) :
    BAVC.leafCom iv key i = prg key iv (i + BAVC.numLeaves - 1).toUInt32 0 2 ∧
      (i + BAVC.numLeaves - 1).toUInt32.toNat ∈ tweaks .leaf := by
  refine ⟨rfl, ?_⟩
  simp only [BAVC.tau] at hi
  rw [numLeaves_eq, toNat_toUInt32 (by simp [L]; omega)]
  simp [tweaks, L, τ]; omega

/-- ConvertToVOLE of vector `i < τ` (`convertToVole`) uses tweak `2³¹ + i`, in the VOLE range. -/
theorem vole_tweak {i : ℕ} (hi : i < BAVC.tau) :
    (((1 : UInt32) <<< 31) + i.toUInt32).toNat = 2 ^ 31 + i ∧ 2 ^ 31 + i ∈ tweaks .vole := by
  simp only [BAVC.tau] at hi
  refine ⟨?_, by simp [tweaks, τ]; omega⟩
  rw [UInt32.toNat_add, toNat_toUInt32 (by omega)]
  have : ((1 : UInt32) <<< 31).toNat = 2 ^ 31 := by decide
  rw [this, Nat.mod_eq_of_lt (by omega)]

/-- **Role separation of the executable PRG inputs.** Two CTR blocks under the same `iv` whose
tweaks lie in the ranges of different roles are different, whatever their counters
(`Commitments.role_inputs_ne` through `lanes_ctrBlock`). -/
theorem ctrBlock_ne_of_roles (iv : ByteArray) {r s : Role} (hrs : r ≠ s) {t t' c c' : UInt32}
    (ht : t.toNat ∈ tweaks r) (ht' : t'.toNat ∈ tweaks s) : ctrBlock iv c t ≠ ctrBlock iv c' t' :=
  fun h => role_inputs_ne (lanes iv) hrs ht ht' c.toNat_lt c'.toNat_lt (by
    rw [← lanes_ctrBlock, ← lanes_ctrBlock, h])

end VoleMole.Verifier.Bridge
