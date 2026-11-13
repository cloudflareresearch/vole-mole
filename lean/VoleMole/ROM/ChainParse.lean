import VoleMole.ROM.Queried
import VoleMole.Verifier.Bridge.Prover

/-!
# Reading a chain's data off the verifier's hash inputs (plan M6, "same chain", item 4)

The "same chain" identification (`ROM/CipherChain.lean`) computes the data a chain commits to from
the hash inputs alone: the `H₂¹` input `x`, the `H₂²` input `y`, the `H₂³` input `z`. Here are the
parsers and their inverse lemmas, for inputs built by the verifier (`chal1Input`, `chal2Input`,
`chal3Input`) from a well-formed proof (`Proof.checkFormat`: the right length):

* `x = mu₁ ‖ com ‖ c₁…c₁₆ ‖ c_mult ‖ iv_pre ‖ binder₁ ‖ 9`: `xCom x` (bytes `32 … 64`), `xPre x` (the
  corrections and `c_mult`, the first `o₂` bytes of the proof), `xIvPre x`;
* `y = chal1 ‖ ũ ‖ h_V ‖ [mu] ‖ binder₂ ‖ d ‖ 10`: `yChal1`, `yVc` (`ũ`), `yHV` (the four field
  elements of `h_V`), `yCorr` (`d`, read from the end);
* `z = chal2 ‖ check ‖ ã ‖ ctr ‖ 11`: `zChal2`, `zCheck`, `zQs` (`ã`).

The proof's fields are at fixed offsets (`Params.field?`, `field_corrections` …), so the first
`o` bytes of a proof determine every field that ends before `o` (`field_extract_zero`); the parsed
pieces concatenate to such prefixes (`xPre_chal1Input`, …).
-/

namespace VoleMole.ROM

open VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge

/-! ## Bytes -/

lemma extract_append3 {A B C : ByteArray} {i j : ℕ} (hi : i = A.size) (hj : j = A.size + B.size) :
    (A ++ B ++ C).extract i j = B := by
  subst hi hj
  rw [ByteArray.append_assoc]
  have h := @ByteArray.extract_append_size_add A (B ++ C) 0 B.size
  rw [Nat.add_zero] at h
  rw [h, ByteArray.extract_append_eq_left rfl]

lemma extract_append_of_le {A B : ByteArray} {i j : ℕ} (hj : j ≤ A.size) :
    (A ++ B).extract i j = A.extract i j := by
  rw [ByteArray.extract_append, Nat.sub_eq_zero_of_le hj,
    (ByteArray.extract_eq_empty_iff (b := B) (i := i - A.size) (j := 0)).2 (by simp),
    ByteArray.append_empty]

lemma extract_append_right' {A B : ByteArray} {i j : ℕ} (hi : A.size ≤ i) :
    (A ++ B).extract i j = B.extract (i - A.size) (j - A.size) := by
  rw [ByteArray.extract_append, (ByteArray.extract_eq_empty_iff (b := A)).2 (by omega),
    ByteArray.empty_append]

lemma extract_zero_of_size {A : ByteArray} {n : ℕ} (h : A.size = n) : A.extract 0 n = A := by
  subst h; exact ByteArray.extract_zero_size

lemma get!_append_left {A B : ByteArray} {k : ℕ} (hk : k < A.size) :
    (A ++ B).get! k = A.get! k := by
  rw [byteArray_get!_eq, byteArray_get!_eq, ByteArray.data_append,
    Array.getElem?_append_left (by simpa using hk)]

lemma get!_append_right (A B : ByteArray) (k : ℕ) : (A ++ B).get! (A.size + k) = B.get! k := by
  rw [byteArray_get!_eq, byteArray_get!_eq, ByteArray.data_append,
    Array.getElem?_append_right (by simp)]
  simp

lemma get!_push_left {A : ByteArray} (b : UInt8) {k : ℕ} (hk : k < A.size) :
    (A.push b).get! k = A.get! k := by
  rw [byteArray_get!_eq, byteArray_get!_eq, ByteArray.data_push,
    Array.getElem?_push_lt (by simpa using hk), Array.getElem?_eq_getElem (by simpa using hk)]

/-! ## Field elements in bytes -/

/-- A little-endian word is determined by its 8 bytes. -/
lemma word_congr {b b' : ByteArray} {o o' : ℕ} (h : ∀ j < 8, b.get! (o + j) = b'.get! (o' + j)) :
    W128.word b o = W128.word b' o' := by
  apply UInt64.toNat_inj.1
  apply Nat.eq_of_testBit_eq
  intro s
  by_cases hs : s < 64
  · rw [word_testBit _ _ _ hs, word_testBit _ _ _ hs, h _ (by omega)]
  · have h1 : ∀ x : UInt64, x.toNat.testBit s = false := fun x =>
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le x.toNat_lt
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [h1, h1]

/-- A field element read from bytes is determined by its 16 bytes. -/
lemma gfOfBytes_congr {b b' : ByteArray} {o o' : ℕ}
    (h : ∀ j < 16, b.get! (o + j) = b'.get! (o' + j)) : gfOfBytes b o = gfOfBytes b' o' := by
  simp only [gfOfBytes, W128.ofBytes, W128.toGF]
  rw [word_congr fun j hj => h j (by omega),
    word_congr (o := o + 8) (o' := o' + 8) fun j hj => by
      rw [Nat.add_assoc, Nat.add_assoc]; exact h (8 + j) (by omega)]

/-- **A field element written as bytes reads back.** -/
lemma gfOfBytes_gfToBytes (a : GF128) : gfOfBytes (gfToBytes a) 0 = a := by
  have hb : gfToBytes a = bytesOfWords #[a.lo, a.hi] := rfl
  simp only [gfOfBytes, W128.ofBytes, W128.toGF]
  rw [hb, show (0 : ℕ) = 8 * 0 from rfl, word_bytesOfWords _ (by simp),
    show 8 * 0 + 8 = 8 * 1 from rfl, word_bytesOfWords _ (by simp)]
  rfl

lemma size_gfToBytes (a : GF128) : (gfToBytes a).size = 16 := by
  have hb : gfToBytes a = bytesOfWords #[a.lo, a.hi] := rfl
  rw [hb, bytesOfWords_size]
  rfl

/-- A field element at offset `A.size` of `A ++ gfToBytes a ++ B` reads back. -/
lemma gfOfBytes_mid (A B : ByteArray) (a : GF128) :
    gfOfBytes (A ++ gfToBytes a ++ B) A.size = a := by
  conv_rhs => rw [← gfOfBytes_gfToBytes a]
  refine gfOfBytes_congr fun j hj => ?_
  rw [get!_append_left (by rw [ByteArray.size_append, size_gfToBytes]; omega), get!_append_right,
    Nat.zero_add]

lemma gfOfBytes_push (Y : ByteArray) (b : UInt8) {n : ℕ} (h : n + 16 ≤ Y.size) :
    gfOfBytes (Y.push b) n = gfOfBytes Y n :=
  gfOfBytes_congr fun j hj => get!_push_left b (by omega)

lemma gfOfBytes_append_left (Y Z : ByteArray) {n : ℕ} (h : n + 16 ≤ Y.size) :
    gfOfBytes (Y ++ Z) n = gfOfBytes Y n :=
  gfOfBytes_congr fun j hj => get!_append_left (by omega)

lemma gfOfBytes_append_right (Y Z : ByteArray) (n : ℕ) :
    gfOfBytes (Y ++ Z) (Y.size + n) = gfOfBytes Z n :=
  gfOfBytes_congr fun j hj => by rw [Nat.add_assoc, get!_append_right]

lemma gfOfBytes_append_right' (Y Z : ByteArray) {m : ℕ} (n : ℕ) (hm : m = Y.size) :
    gfOfBytes (Y ++ Z) (m + n) = gfOfBytes Z n := by
  subst hm; exact gfOfBytes_append_right Y Z n

/-! ## The proof layout -/

end VoleMole.ROM

namespace VoleMole.Verifier.Params

variable (p : Params)

/-- The end of `c_mult` (= the start of `ũ`). -/
def o₂ : ℕ := 16 * p.correctionBytes + p.nMask * p.nMultBytes
/-- The end of `d` (= the start of `ã`). -/
def o₄ : ℕ := p.o₂ + 64 + p.witnessBytes
/-- The end of `ã`. -/
def o₅ : ℕ := p.o₄ + (p.qsDegree - 1) * 16
/-- The start of `iv_pre`. -/
def o₇ : ℕ := p.o₅ + BAVC.openSize + 16

lemma field_corrections : p.field? "corrections" = some (0, 16 * p.correctionBytes) := by
  simp [field?, fieldSizes]

lemma field_cmult :
    p.field? "cmult" = some (16 * p.correctionBytes, p.nMask * p.nMultBytes) := by
  simp [field?, fieldSizes]

lemma field_voleCheck : p.field? "vole_check" = some (p.o₂, 64) := by
  simp [field?, fieldSizes, o₂]

lemma field_correction : p.field? "correction" = some (p.o₂ + 64, p.witnessBytes) := by
  simp [field?, fieldSizes, o₂]

lemma field_qsProof : p.field? "qs_proof" = some (p.o₄, (p.qsDegree - 1) * 16) := by
  simp [field?, fieldSizes, o₂, o₄]

lemma field_ivPre : p.field? "iv_pre" = some (p.o₇, 16) := by
  simp [field?, fieldSizes, o₂, o₄, o₅, o₇]

lemma field_ctr : p.field? "ctr" = some (p.o₇ + 16, 4) := by
  simp [field?, fieldSizes, o₂, o₄, o₅, o₇]

lemma proofBytes_eq : p.proofBytes = p.o₇ + 20 := by
  simp [proofBytes, fieldSizes, o₂, o₄, o₅, o₇]
  omega

end VoleMole.Verifier.Params

namespace VoleMole.ROM

open VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge

/-- A field that ends before `N` is read off the first `N` bytes. -/
lemma field_extract_zero (p : Params) (b : ByteArray) {k : String} {off n N : ℕ}
    (hk : p.field? k = some (off, n)) (hN : off + n ≤ N) :
    Proof.field ⟨p, b.extract 0 N⟩ k = Proof.field ⟨p, b⟩ k := by
  simp only [Proof.field, hk, ByteArray.extract_extract, Nat.zero_add]
  congr 1
  omega

lemma field_eq (pf : Proof) {k : String} {off n : ℕ} (hk : pf.params.field? k = some (off, n)) :
    pf.field k = pf.bytes.extract off (off + n) := by
  simp [Proof.field, hk]

lemma size_field (pf : Proof) (hf : pf.checkFormat = true) {k : String} {off n : ℕ}
    (hk : pf.params.field? k = some (off, n)) (hN : off + n ≤ pf.params.proofBytes) :
    (pf.field k).size = n := by
  rw [field_eq pf hk, ByteArray.size_extract]
  simp only [Proof.checkFormat, Bool.and_eq_true, beq_iff_eq] at hf
  rw [hf.1]
  omega

/-! ## The parsers -/

/-- The `com` field of an `H₂¹` input. -/
def xCom (x : ByteArray) : ByteArray := x.extract 32 64

/-- The corrections and `c_mult` of an `H₂¹` input (the first `o₂` bytes of the proof). -/
def xPre (p : Params) (x : ByteArray) : ByteArray := x.extract 64 (64 + p.o₂)

/-- The `iv_pre` field of an `H₂¹` input. -/
def xIvPre (p : Params) (x : ByteArray) : ByteArray := x.extract (64 + p.o₂) (64 + p.o₂ + 16)

/-- The `chal1` field of an `H₂²` input. -/
def yChal1 (y : ByteArray) : ByteArray := y.extract 0 136

/-- The `ũ` field of an `H₂²` input. -/
def yVc (y : ByteArray) : ByteArray := y.extract 136 200

/-- The `h_V` field of an `H₂²` input, as four field elements. -/
def yHV (y : ByteArray) : Array GF128 :=
  #[gfOfBytes y 200, gfOfBytes y 216, gfOfBytes y 232, gfOfBytes y 248]

/-- The `d` field of an `H₂²` input (its last `ℓ/8` bytes before the domain byte). -/
def yCorr (p : Params) (y : ByteArray) : ByteArray :=
  y.extract (y.size - 1 - p.witnessBytes) (y.size - 1)

/-- The `chal2` field of an `H₂³` input. -/
def zChal2 (z : ByteArray) : ByteArray := z.extract 0 56

/-- The check value of an `H₂³` input. -/
def zCheck (z : ByteArray) : GF128 := gfOfBytes z 56

/-- The `ã` field of an `H₂³` input. -/
def zQs (p : Params) (z : ByteArray) : ByteArray := z.extract 72 (72 + (p.qsDegree - 1) * 16)

/-! ## The parsers invert the verifier's inputs -/

section Inverse

lemma size_bytes {pf : Proof} (hf : pf.checkFormat = true) :
    pf.bytes.size = pf.params.o₇ + 20 := by
  simp only [Proof.checkFormat, Bool.and_eq_true, beq_iff_eq] at hf
  rw [hf.1, Params.proofBytes_eq]

lemma corrections_eq (pf : Proof) :
    pf.corrections = pf.bytes.extract 0 (16 * pf.params.correctionBytes) := by
  rw [Proof.corrections, field_eq pf (Params.field_corrections _), Nat.zero_add]

lemma cmult_eq (pf : Proof) :
    pf.cmult = pf.bytes.extract (16 * pf.params.correctionBytes) pf.params.o₂ := by
  rw [Proof.cmult, field_eq pf (Params.field_cmult _)]
  rfl

lemma voleCheck_eq (pf : Proof) :
    pf.voleCheck = pf.bytes.extract pf.params.o₂ (pf.params.o₂ + 64) := by
  rw [Proof.voleCheck, field_eq pf (Params.field_voleCheck _)]

lemma correction_eq (pf : Proof) :
    pf.correction = pf.bytes.extract (pf.params.o₂ + 64) pf.params.o₄ := by
  rw [Proof.correction, field_eq pf (Params.field_correction _)]
  rfl

lemma qsProof_eq (pf : Proof) : pf.qsProof = pf.bytes.extract pf.params.o₄ pf.params.o₅ := by
  rw [Proof.qsProof, field_eq pf (Params.field_qsProof _)]
  rfl

lemma ivPre_eq (pf : Proof) : pf.ivPre = pf.bytes.extract pf.params.o₇ (pf.params.o₇ + 16) := by
  rw [Proof.ivPre, field_eq pf (Params.field_ivPre _)]

lemma o₂_le (p : Params) : 16 * p.correctionBytes ≤ p.o₂ := by
  unfold Params.o₂; omega

lemma o₇_eq (p : Params) : p.o₇ = p.o₂ + 64 + p.witnessBytes + (p.qsDegree - 1) * 16 +
    BAVC.openSize + 16 := by
  unfold Params.o₇ Params.o₅ Params.o₄; rfl

variable {pf : Proof} (hf : pf.checkFormat = true)
include hf

lemma size_corrections : pf.corrections.size = 16 * pf.params.correctionBytes := by
  rw [corrections_eq, ByteArray.size_extract, size_bytes hf, o₇_eq]
  have := o₂_le pf.params
  omega

lemma size_cmult : pf.cmult.size = pf.params.nMask * pf.params.nMultBytes := by
  rw [cmult_eq, ByteArray.size_extract, size_bytes hf, o₇_eq]
  unfold Params.o₂
  omega

lemma size_voleCheck : pf.voleCheck.size = 64 := by
  rw [voleCheck_eq, ByteArray.size_extract, size_bytes hf, o₇_eq]
  omega

lemma size_correction : pf.correction.size = pf.params.witnessBytes := by
  rw [correction_eq, ByteArray.size_extract, size_bytes hf, o₇_eq]
  unfold Params.o₄
  omega

lemma size_qsProof : pf.qsProof.size = (pf.params.qsDegree - 1) * 16 := by
  rw [qsProof_eq, ByteArray.size_extract, size_bytes hf, o₇_eq]
  unfold Params.o₅ Params.o₄
  omega

lemma size_ivPre : pf.ivPre.size = 16 := by
  rw [ivPre_eq, ByteArray.size_extract, size_bytes hf]
  omega

omit hf in
/-- The corrections and `c_mult` are the first `o₂` bytes. -/
lemma corrections_append_cmult : pf.corrections ++ pf.cmult = pf.bytes.extract 0 pf.params.o₂ := by
  rw [corrections_eq, cmult_eq, ByteArray.extract_append_extract, Nat.min_eq_left (Nat.zero_le _),
    Nat.max_eq_right (o₂_le pf.params)]

omit hf in
/-- The proof's first `o₄` bytes are the corrections, `c_mult`, `ũ` and `d`. -/
lemma prefix_o₄ : pf.bytes.extract 0 pf.params.o₂ ++ pf.voleCheck ++ pf.correction =
    pf.bytes.extract 0 pf.params.o₄ := by
  rw [voleCheck_eq, correction_eq, ByteArray.extract_append_extract, Nat.min_eq_left (Nat.zero_le _),
    Nat.max_eq_right (by omega), ByteArray.extract_append_extract, Nat.min_eq_left (Nat.zero_le _),
    Nat.max_eq_right (by unfold Params.o₄; omega)]

omit hf in
/-- The proof's first `o₅` bytes, with `ã`. -/
lemma prefix_o₅ : pf.bytes.extract 0 pf.params.o₄ ++ pf.qsProof = pf.bytes.extract 0 pf.params.o₅ := by
  rw [qsProof_eq, ByteArray.extract_append_extract, Nat.min_eq_left (Nat.zero_le _),
    Nat.max_eq_right (by unfold Params.o₅; omega)]

variable {mu1 com b1 : ByteArray} (hmu : mu1.size = 32) (hcom : com.size = 32)
include hmu hcom

omit hf in
lemma xCom_chal1Input : xCom (chal1Input pf mu1 com b1) = com := by
  show (chal1Input pf mu1 com b1).extract 32 (32 + 32) = com
  simp only [chal1Input, ByteArray.append_assoc]
  exact extract_mid_append_push _ _ _ _ hmu hcom

lemma xPre_chal1Input :
    xPre pf.params (chal1Input pf mu1 com b1) = pf.bytes.extract 0 pf.params.o₂ := by
  have hc := size_corrections hf
  have hm := size_cmult hf
  have h2 : (pf.corrections ++ pf.cmult).size = pf.params.o₂ := by
    rw [ByteArray.size_append, hc, hm]; rfl
  simp only [xPre, chal1Input]
  rw [show mu1 ++ com ++ pf.corrections ++ pf.cmult ++ pf.ivPre ++ b1 =
      (mu1 ++ com) ++ (pf.corrections ++ pf.cmult) ++ (pf.ivPre ++ b1) by
    simp only [ByteArray.append_assoc]]
  rw [extract_push_of_le _ _ (by simp only [ByteArray.size_append, hmu, hcom, h2]; omega),
    extract_append3 (by simp [hmu, hcom]) (by rw [h2]; simp [hmu, hcom]),
    corrections_append_cmult]

lemma xIvPre_chal1Input : xIvPre pf.params (chal1Input pf mu1 com b1) = pf.ivPre := by
  have hc := size_corrections hf
  have hm := size_cmult hf
  have hi := size_ivPre hf
  have h2 : (mu1 ++ com ++ pf.corrections ++ pf.cmult).size = 64 + pf.params.o₂ := by
    simp only [ByteArray.size_append, hmu, hcom, hc, hm, Params.o₂]; omega
  simp only [xIvPre, chal1Input]
  rw [extract_push_of_le _ _ (by simp only [ByteArray.size_append] at h2 ⊢; rw [hi]; omega)]
  exact extract_append3 h2.symm (by rw [h2, hi])

end Inverse

section InverseY

/-- The bytes of `h_V` in the `H₂²` input. -/
abbrev hvBytes (h : Array GF128) : ByteArray :=
  h.foldl (fun acc x => acc ++ gfToBytes x) ByteArray.empty

variable {pf : Proof} (hf : pf.checkFormat = true) {c1 muD b2 : ByteArray} (hV : Array GF128)
  (hc1 : c1.size = 136)
include hc1

lemma yChal1_chal2Input : yChal1 (chal2Input pf c1 hV muD b2) = c1 := by
  simp only [yChal1, chal2Input, ByteArray.append_assoc]
  exact extract_zero_append_push _ _ _ hc1

include hf in
lemma yVc_chal2Input : yVc (chal2Input pf c1 hV muD b2) = pf.voleCheck := by
  show (chal2Input pf c1 hV muD b2).extract 136 (136 + 64) = pf.voleCheck
  simp only [chal2Input, ByteArray.append_assoc]
  exact extract_mid_append_push c1 pf.voleCheck _ 10 hc1 (size_voleCheck hf)

omit hc1 in
include hf in
lemma yCorr_chal2Input : yCorr pf.params (chal2Input pf c1 hV muD b2) = pf.correction := by
  have hc := size_correction hf
  simp only [yCorr, chal2Input, ByteArray.size_push]
  generalize c1 ++ pf.voleCheck ++ hvBytes hV ++ muD ++ b2 = A
  rw [Nat.add_sub_cancel, extract_push_of_le _ _ le_rfl, ByteArray.size_append, hc,
    Nat.add_sub_cancel]
  exact ByteArray.extract_append_eq_right rfl (by rw [hc])

omit hc1 in
/-- The bytes of four field elements, read back. -/
lemma gfOfBytes_hvBytes (a₀ a₁ a₂ a₃ : GF128) :
    gfOfBytes (hvBytes #[a₀, a₁, a₂, a₃]) 0 = a₀ ∧ gfOfBytes (hvBytes #[a₀, a₁, a₂, a₃]) 16 = a₁ ∧
      gfOfBytes (hvBytes #[a₀, a₁, a₂, a₃]) 32 = a₂ ∧
      gfOfBytes (hvBytes #[a₀, a₁, a₂, a₃]) 48 = a₃ := by
  have e : hvBytes #[a₀, a₁, a₂, a₃] =
      ByteArray.empty ++ gfToBytes a₀ ++ gfToBytes a₁ ++ gfToBytes a₂ ++ gfToBytes a₃ := rfl
  have s := size_gfToBytes
  have s0 : (ByteArray.empty ++ gfToBytes a₀).size = 16 := by
    rw [ByteArray.size_append, s]; rfl
  have s1 : (ByteArray.empty ++ gfToBytes a₀ ++ gfToBytes a₁).size = 32 := by
    rw [ByteArray.size_append, s0, s]
  have s2 : (ByteArray.empty ++ gfToBytes a₀ ++ gfToBytes a₁ ++ gfToBytes a₂).size = 48 := by
    rw [ByteArray.size_append, s1, s]
  rw [e]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [gfOfBytes_append_left _ _ (by omega), gfOfBytes_append_left _ _ (by omega),
      gfOfBytes_append_left _ _ (by omega),
      show (0 : ℕ) = ByteArray.empty.size + 0 from rfl, gfOfBytes_append_right]
    all_goals exact gfOfBytes_gfToBytes _
  · rw [gfOfBytes_append_left _ _ (by omega), gfOfBytes_append_left _ _ (by omega),
      gfOfBytes_append_right' _ _ 0 s0.symm]
    all_goals exact gfOfBytes_gfToBytes _
  · rw [gfOfBytes_append_left _ _ (by omega), gfOfBytes_append_right' _ _ 0 s1.symm]
    all_goals exact gfOfBytes_gfToBytes _
  · rw [gfOfBytes_append_right' _ _ 0 s2.symm]
    all_goals exact gfOfBytes_gfToBytes _

include hf in
/-- **`h_V` read back from the `H₂²` input.** -/
lemma yHV_chal2Input (h4 : hV.size = 4) : yHV (chal2Input pf c1 hV muD b2) = hV := by
  have hvc := size_voleCheck hf
  have e4 : hV = #[hV[0]!, hV[1]!, hV[2]!, hV[3]!] := by
    apply Array.ext
    · simp [h4]
    · intro i h1 h2
      simp only [h4] at h1
      interval_cases i <;> simp [getElem!_pos, h4]
  have hbs : (hV.foldl (fun acc x => acc ++ gfToBytes x) ByteArray.empty).size = 64 := by
    rw [e4]
    show (ByteArray.empty ++ gfToBytes _ ++ gfToBytes _ ++ gfToBytes _ ++ gfToBytes _).size = 64
    simp only [ByteArray.size_append, size_gfToBytes]
    rfl
  have hA : (c1 ++ pf.voleCheck).size = 200 := by rw [ByteArray.size_append, hc1, hvc]
  have key : ∀ k < 4, gfOfBytes (chal2Input pf c1 hV muD b2) (200 + 16 * k) =
      gfOfBytes (hvBytes hV) (16 * k) := by
    intro k hk
    simp only [chal2Input]
    rw [gfOfBytes_push _ _ (by simp only [ByteArray.size_append, hA, hbs]; omega),
      gfOfBytes_append_left _ _ (by simp only [ByteArray.size_append, hA, hbs]; omega),
      gfOfBytes_append_left _ _ (by simp only [ByteArray.size_append, hA, hbs]; omega),
      gfOfBytes_append_left _ _ (by simp only [ByteArray.size_append, hA, hbs]; omega),
      gfOfBytes_append_right' _ _ _ hA.symm]
  obtain ⟨g0, g1, g2, g3⟩ := gfOfBytes_hvBytes hV[0]! hV[1]! hV[2]! hV[3]!
  rw [← e4] at g0 g1 g2 g3
  have k0 : gfOfBytes (chal2Input pf c1 hV muD b2) 200 = hV[0]! := (key 0 (by norm_num)).trans g0
  have k1 : gfOfBytes (chal2Input pf c1 hV muD b2) 216 = hV[1]! := (key 1 (by norm_num)).trans g1
  have k2 : gfOfBytes (chal2Input pf c1 hV muD b2) 232 = hV[2]! := (key 2 (by norm_num)).trans g2
  have k3 : gfOfBytes (chal2Input pf c1 hV muD b2) 248 = hV[3]! := (key 3 (by norm_num)).trans g3
  simp only [yHV]
  rw [k0, k1, k2, k3]
  exact e4.symm

end InverseY

section InverseZ

variable {pf : Proof} (hf : pf.checkFormat = true) {c2 : ByteArray} (chk : GF128)
  (hc2 : c2.size = 56)
include hc2

lemma zChal2_chal3Input : zChal2 (chal3Input pf c2 chk) = c2 := by
  simp only [zChal2, chal3Input, ByteArray.append_assoc]
  exact extract_zero_append_push _ _ _ hc2

lemma zCheck_chal3Input : zCheck (chal3Input pf c2 chk) = chk := by
  have hA : (c2 ++ gfToBytes chk).size = 72 := by rw [ByteArray.size_append, hc2, size_gfToBytes]
  simp only [zCheck, chal3Input]
  rw [gfOfBytes_push _ _ (by simp only [ByteArray.size_append] at hA ⊢; omega),
    gfOfBytes_append_left _ _ (by simp only [ByteArray.size_append] at hA ⊢; omega),
    gfOfBytes_append_left _ _ (by omega), show (56 : ℕ) = c2.size + 0 by rw [hc2],
    gfOfBytes_append_right, gfOfBytes_gfToBytes]

include hf in
lemma zQs_chal3Input : zQs pf.params (chal3Input pf c2 chk) = pf.qsProof := by
  have hA : (c2 ++ gfToBytes chk).size = 72 := by rw [ByteArray.size_append, hc2, size_gfToBytes]
  have hq := size_qsProof hf
  simp only [zQs, chal3Input]
  rw [extract_push_of_le _ _ (by simp only [ByteArray.size_append] at hA ⊢; omega)]
  exact extract_append3 hA.symm (by rw [hA, hq])

end InverseZ

end VoleMole.ROM
