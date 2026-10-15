import VoleMole.Verifier.Bridge.Columns
import VoleMole.Verifier.Bridge.Relations
import VoleMole.Verifier.Prover

/-!
# Bridge: completeness of the executable verifier on the executable prover's output

`Verifier/Prover.lean` computes the prover's side of every step by reusing the verifier's step
functions at `Δ = 0` and, for QuickSilver, at `d + 1` sample points. Here: what this output
satisfies, for every `Δ` the grinding may produce.

* **Bytes and layout.** `word_testBit`, `bytesOfWords_get`, `wbit_wordsOf_bytesOfWords`,
  `word_bytesOfWords`, `gfOfBytes_gfsToBytes`, `gfOfBytes_zeros`: the little-endian conversions of
  the proof format read back what was written. `fields_assemble`: each field of
  `Prover.assemble` is the (fitted) field it was given; `correctionOf_concat`: the verifier's
  `c_i` are the prover's.
* **The VOLE correlation** (`prover_column`, `prover_row`). With the prover's corrections
  `c_i = u^{(0)} ⊕ u^{(i)}` (`proverCorr`) and leaf keys, the verifier's key column `p_i + b` is the
  prover's tag column plus `Δ_{p_i+b}·u` on the `ℓ'` corrected rows (from `Bridge/Columns`'s
  `treeColumns_affine`: the corrected `u^{(i)}` is `u = u^{(0)}`), so each CRT-lifted row is
  `q_r = v_r + u_r·Δ'`.
* **The VOLE check** (`voleHash_complete`). If the rows and the masks are `v + u·Δ'`, the
  verifier's VOLEHash corrected by `Δ'·ũ` (the prover's `ũ`, the VOLEHash of `u`) is the
  prover's `h_V` (`horner_lin`: Horner is linear), so `chal2` agrees.
* **QuickSilver** (`qsProve_complete`). If `Prover.qsProve` succeeds, then for every `Δ' ≠ 0` the
  verifier's check value at the prover's keys `v_j + w_j Δ'`, masks `ṽ_mask + u_mask Δ'` and `ã` is
  `qs_check`. Via `EndToEnd`: the check value is the check polynomial `sysCheckPoly` of the system
  (`qsAt_eq`, from `map_constraintKeys`, `mac_constraintQS`, `map_qsCheck`, `eval_sysCheckPoly`),
  of degree `≤ d` (`sysCheckPoly_natDegree_coeff`); the interpolated polynomial agrees with it on
  the `d + 1` sample points the prover checked, so equals it (`Lagrange`); with the prover's
  `ã_{i−1} = g_i` the non-constant coefficients cancel in characteristic 2, and `g_d = 0` was
  checked.
* **Completeness** (`verify_proveCommit`, `verify_prove`, `moussakaIssue_complete`,
  `moussakaRedeem_complete`, `ratatouilleIssue_complete`, `ratatouilleSpend_complete`,
  `pomfritRedeem_complete`): if the prover returns a proof, `verify` accepts it. Assumed:
  - `HashesWF Hs`: the hash functions have the domains' output lengths (`hashesWF_shake`: SHAKE128
    has them);
  - `BAVCComplete`: an opening of the prover's GGM tree reconstructs its leaf keys off the hidden
    leaves and its commitments (an imperative walk over the 4607 nodes, not proved);
  - `CrtComplete`: the verifier's CRT masks are `ṽ_mask + u_mask·Δ'` for the prover's commitment
    (the garbled gate labels and the bilinear identity of the CRT tables, not proved; the rows are);
  - `Δ' ≠ 0` for the ground `Δ` (probability `2⁻¹²⁰`; neither the C++ prover nor the Lean one
    tests it).
  `lake exe prover_vectors` checks the two correctness assumptions on every proof it produces
  (`ProverKats.checkCorrelation`). The witness need not be assumed to satisfy the relation:
  `Prover.qsProve` refuses otherwise.
-/

open Finset Polynomial

namespace VoleMole.Verifier.Bridge

open VoleMole.Arith VoleMole.Verifier VoleMole.EndToEnd VoleMole.EndToEnd.QSExprMac

noncomputable section

/-! ## Bytes and words -/

lemma testBit_byte_shift (x : UInt8) (j s : ℕ) (hj : j < 8) (hs : s < 64) :
    ((x.toUInt64 <<< (8 * j).toUInt64).toNat.testBit s) =
      (decide (s / 8 = j) && x.toNat.testBit (s % 8)) := by
  have hx : x.toNat < 256 := x.toNat_lt
  have h8 : (8 * j).toUInt64.toNat % 64 = 8 * j := by
    simp [Nat.toUInt64, UInt64.toNat_ofNat]; omega
  rw [UInt64.toNat_shiftLeft, h8, UInt8.toNat_toUInt64, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft]
  by_cases hsj : s / 8 = j
  · have : s - 8 * j = s % 8 := by omega
    simp [hs, hsj, this, show 8 * j ≤ s by omega]
  · simp only [hsj, decide_false, Bool.false_and]
    by_cases hle : 8 * j ≤ s
    · have h2 : 8 ≤ s - 8 * j := by omega
      have : x.toNat.testBit (s - 8 * j) = false :=
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (by
          calc 256 = 2 ^ 8 := by norm_num
            _ ≤ 2 ^ (s - 8 * j) := Nat.pow_le_pow_right (by norm_num) h2))
      simp [this]
    · simp [hle]

/-- `W128.word` as a fold. -/
lemma word_eq_foldl (b : ByteArray) (off : ℕ) :
    W128.word b off = (List.range 8).foldl
      (fun (w : UInt64) j => w ||| ((b.get! (off + j)).toUInt64 <<< (8 * j).toUInt64)) 0 := by
  simp only [W128.word, Id.run, bind_pure]
  rw [forIn_range_foldl _ _ _ (fun j (w : UInt64) => w ||| ((b.get! (off + j)).toUInt64 <<<
    (8 * j).toUInt64)) fun _ _ => rfl]
  rfl

/-- **Bit `s` of the little-endian word at `off`** is bit `s % 8` of byte `off + s / 8`. -/
theorem word_testBit (b : ByteArray) (off s : ℕ) (hs : s < 64) :
    (W128.word b off).toNat.testBit s = (b.get! (off + s / 8)).toNat.testBit (s % 8) := by
  have hstep : ∀ (l : List ℕ) (acc : UInt64), (∀ j ∈ l, j < 8) →
      (l.foldl (fun (w : UInt64) j => w ||| ((b.get! (off + j)).toUInt64 <<< (8 * j).toUInt64))
        acc).toNat.testBit s =
        (acc.toNat.testBit s || l.any fun j => decide (s / 8 = j) &&
          (b.get! (off + j)).toNat.testBit (s % 8)) := by
    intro l
    induction l with
    | nil => simp
    | cons j l ih =>
      intro acc hl
      rw [List.foldl_cons, ih _ fun j' hj' => hl j' (List.mem_cons_of_mem _ hj'),
        UInt64.toNat_or, Nat.testBit_or, testBit_byte_shift _ _ _ (hl j (by simp)) hs]
      simp [Bool.or_assoc]
  rw [word_eq_foldl, hstep _ _ fun j hj => List.mem_range.1 hj]
  have h8 : s / 8 < 8 := by omega
  simp only [UInt64.toNat_zero, Nat.zero_testBit, Bool.false_or]
  rw [Bool.eq_iff_iff, List.any_eq_true]
  constructor
  · rintro ⟨j, _, hj⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
    rw [hj.1]; exact hj.2
  · intro h
    exact ⟨s / 8, List.mem_range.2 h8, by simp [h]⟩

/-- The 8 little-endian bytes of a word. -/
def leBytes (w : UInt64) : List UInt8 :=
  (List.range 8).map fun j => (w >>> (8 * j).toUInt64).toUInt8

lemma leBytes_length (w : UInt64) : (leBytes w).length = 8 := by simp [leBytes]

lemma foldl_push_data {α : Type} (f : α → UInt8) :
    ∀ (l : List α) (o : ByteArray),
      (l.foldl (fun o j => o.push (f j)) o).data = o.data ++ (l.map f).toArray
  | [], o => by simp
  | j :: l, o => by
    rw [List.foldl_cons, foldl_push_data f l]
    simp

lemma pushWord_data (out : ByteArray) (w : UInt64) :
    (W128.pushWord out w).data = out.data ++ (leBytes w).toArray := by
  simp only [W128.pushWord, Id.run, bind_pure]
  rw [forIn_range_foldl _ _ _ (fun j (o : ByteArray) => o.push (w >>> (8 * j).toUInt64).toUInt8)
    fun _ _ => rfl]
  exact foldl_push_data _ _ _

lemma bytesOfWords_data (W : Array UInt64) :
    (bytesOfWords W).data = (W.toList.flatMap leBytes).toArray := by
  have h : ∀ (l : List UInt64) (o : ByteArray),
      (l.foldl W128.pushWord o).data = o.data ++ (l.flatMap leBytes).toArray := by
    intro l; induction l with
    | nil => simp
    | cons w l ih => intro o; rw [List.foldl_cons, ih, pushWord_data]; simp
  rw [bytesOfWords, ← Array.foldl_toList, h]
  exact Array.empty_append

lemma getElem?_flatMap_leBytes :
    ∀ (L : List UInt64) (k : ℕ),
      (L.flatMap leBytes)[k]? = L[k / 8]?.map fun w => (leBytes w)[k % 8]!
  | [], k => by simp
  | w :: L, k => by
    rw [List.flatMap_cons, List.getElem?_append, leBytes_length]
    by_cases hk : k < 8
    · simp [hk, Nat.div_eq_of_lt hk, Nat.mod_eq_of_lt hk, leBytes_length, getElem!_pos]
    · simp only [hk, ↓reduceIte]
      rw [getElem?_flatMap_leBytes L]
      have h1 : k / 8 = (k - 8) / 8 + 1 := by omega
      have h2 : k % 8 = (k - 8) % 8 := by omega
      simp [h1, h2]

lemma byteArray_get!_eq (b : ByteArray) (k : ℕ) : b.get! k = (b.data[k]?).getD default := by
  cases b; simp [ByteArray.get!, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]

lemma bytesOfWords_size (W : Array UInt64) : (bytesOfWords W).size = 8 * W.size := by
  rw [ByteArray.size, bytesOfWords_data, List.size_toArray, List.length_flatMap]
  simp [leBytes_length, List.sum_replicate, mul_comm]

/-- Byte `k` of `bytesOfWords W` is byte `k % 8` of word `k / 8`. -/
lemma bytesOfWords_get (W : Array UInt64) {k : ℕ} (hk : k < 8 * W.size) :
    (bytesOfWords W).get! k = (W[k / 8]! >>> (8 * (k % 8)).toUInt64).toUInt8 := by
  have hq : k / 8 < W.size := by omega
  rw [byteArray_get!_eq, bytesOfWords_data, List.getElem?_toArray, getElem?_flatMap_leBytes,
    Array.getElem?_toList, Array.getElem?_eq_getElem hq]
  simp [leBytes, getElem!_pos, hq, show k % 8 < 8 by omega]

lemma testBit_shiftRight_toUInt8 (w : UInt64) (m t : ℕ) (hm : m < 8) (ht : t < 8) :
    (w >>> (8 * m).toUInt64).toUInt8.toNat.testBit t = w.toNat.testBit (8 * m + t) := by
  have h8 : (8 * m).toUInt64.toNat % 64 = 8 * m := by
    simp [Nat.toUInt64, UInt64.toNat_ofNat]; omega
  rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, h8, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftRight]
  simp [ht, Nat.add_comm]

/-- **Reading words from bytes**: bit `r` of `wordsOf X` is bit `r % 8` of byte `r / 8`. -/
theorem wbit_wordsOf (X : ByteArray) {r : ℕ} (hr : r / 64 < X.size / 8) :
    wbit (wordsOf X) r = (X.get! (r / 8)).toNat.testBit (r % 8) := by
  rw [wbit_eq, wordsOf, getElem!_range_map _ _ hr, word_testBit _ _ _ (Nat.mod_lt _ (by norm_num))]
  have e1 : 8 * (r / 64) + r % 64 / 8 = r / 8 := by omega
  have e2 : r % 64 % 8 = r % 8 := by omega
  rw [e1, e2]

/-- **Writing words as bytes and reading them back**: bit `r < 8 n` of the words read from the
first `n` bytes of `bytesOfWords W` (zero-padded) is bit `r` of `W`. -/
theorem wbit_wordsOf_bytesOfWords (W : Array UInt64) (n : ℕ) (Z : ByteArray) {r : ℕ}
    (hn : n ≤ 8 * W.size) (hr : r < 8 * n) (hX : r / 64 < (n + Z.size) / 8) :
    wbit (wordsOf ((bytesOfWords W).extract 0 n ++ Z)) r = wbit W r := by
  have hsz : ((bytesOfWords W).extract 0 n).size = n := by
    rw [ByteArray.size_extract, bytesOfWords_size]; omega
  rw [wbit_wordsOf _ (by rw [ByteArray.size_append, hsz]; exact hX)]
  have hk : r / 8 < n := by omega
  have hget : ((bytesOfWords W).extract 0 n ++ Z).get! (r / 8) = (bytesOfWords W).get! (r / 8) := by
    have hk' : r / 8 < ((bytesOfWords W).extract 0 n).data.size := by
      rw [← ByteArray.size, hsz]; exact hk
    have hk2 : r / 8 < (bytesOfWords W).size := by rw [bytesOfWords_size]; omega
    rw [byteArray_get!_eq, byteArray_get!_eq, ByteArray.data_append, Array.getElem?_append]
    simp [hk, hk2]
  rw [hget, bytesOfWords_get _ (by omega), wbit_eq,
    testBit_shiftRight_toUInt8 _ _ _ (by omega) (by omega)]
  have e1 : r / 8 / 8 = r / 64 := by omega
  have e2 : 8 * (r / 8 % 8) + r % 8 = r % 64 := by omega
  rw [e1, e2]

/-- **Words written as bytes read back**: the word at byte `8 k` of `bytesOfWords W` is `W[k]`. -/
theorem word_bytesOfWords (W : Array UInt64) {k : ℕ} (hk : k < W.size) :
    W128.word (bytesOfWords W) (8 * k) = W[k]! := by
  apply UInt64.toNat_inj.1
  apply Nat.eq_of_testBit_eq
  intro s
  by_cases hs : s < 64
  · rw [word_testBit _ _ _ hs, bytesOfWords_get _ (by omega),
      testBit_shiftRight_toUInt8 _ _ _ (by omega) (by omega)]
    have e1 : (8 * k + s / 8) / 8 = k := by omega
    have e2 : 8 * ((8 * k + s / 8) % 8) + s % 8 = s := by omega
    rw [e1, e2]
  · have h1 : ∀ x : UInt64, x.toNat.testBit s = false := fun x =>
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le x.toNat_lt
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [h1, h1]

lemma getElem?_flatMap_pair :
    ∀ (xs : List GF128) {i : ℕ} (hi : i < xs.length),
      (xs.flatMap fun x => [x.lo, x.hi])[2 * i]? = some xs[i].lo ∧
        (xs.flatMap fun x => [x.lo, x.hi])[2 * i + 1]? = some xs[i].hi
  | [], _, hi => by simp at hi
  | x :: xs, 0, _ => by simp
  | x :: xs, i + 1, hi => by
    have h := getElem?_flatMap_pair xs (i := i) (by simpa using hi)
    rw [List.flatMap_cons, show 2 * (i + 1) = 2 * i + 1 + 1 by ring,
      show 2 * i + 1 + 1 + 1 = 2 * i + 1 + 1 + 1 from rfl]
    simpa using h

lemma getElem!_flatMap_pair (xs : List GF128) {i : ℕ} (hi : i < xs.length) :
    ((xs.flatMap fun x => [x.lo, x.hi]).toArray[2 * i]! = xs[i].lo) ∧
      ((xs.flatMap fun x => [x.lo, x.hi]).toArray[2 * i + 1]! = xs[i].hi) := by
  have h := getElem?_flatMap_pair xs hi
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, List.getElem?_toArray, h.1, h.2,
    Option.getD_some, and_self]

/-- **Field elements written as bytes read back** (`Prover.gfsToBytes`, `gfOfBytes`). -/
theorem gfOfBytes_gfsToBytes (xs : Array GF128) {i : ℕ} (hi : i < xs.size) :
    gfOfBytes (Prover.gfsToBytes xs) (16 * i) = xs[i]! := by
  have hl : (xs.toList.flatMap fun x => [x.lo, x.hi]).toArray.size = 2 * xs.size := by
    simp [List.length_flatMap, List.sum_replicate, mul_comm]
  have h := getElem!_flatMap_pair xs.toList (i := i) (by simpa using hi)
  simp only [gfOfBytes, W128.ofBytes, W128.toGF, Prover.gfsToBytes]
  rw [show 16 * i = 8 * (2 * i) by ring, show 8 * (2 * i) + 8 = 8 * (2 * i + 1) by ring,
    word_bytesOfWords _ (by omega), word_bytesOfWords _ (by omega), h.1, h.2]
  simp [getElem!_pos, hi]

/-- Zero bytes read as the zero field element. -/
theorem gfOfBytes_zeros (n off : ℕ) : gfOfBytes (Prover.zeros n) off = 0 := by
  have hw : ∀ o, W128.word (Prover.zeros n) o = 0 := fun o => by
    apply UInt64.toNat_inj.1
    apply Nat.eq_of_testBit_eq
    intro s
    by_cases hs : s < 64
    · rw [word_testBit _ _ _ hs]
      have : (Prover.zeros n).get! (o + s / 8) = 0 := by
        rw [byteArray_get!_eq]
        simp only [Prover.zeros, Array.getElem?_replicate]
        split <;> rfl
      simp [this]
    · simp only [UInt64.toNat_zero, Nat.zero_testBit]
      exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (W128.word _ o).toNat_lt
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
  simp only [gfOfBytes, W128.ofBytes, W128.toGF, hw]
  rfl

/-! ## The proof layout -/

theorem foldl_append_eq : ∀ (L : List ByteArray) (acc : ByteArray),
    L.foldl (· ++ ·) acc = acc ++ L.foldl (· ++ ·) ByteArray.empty
  | [], acc => by simp
  | b :: L, acc => by
    simp only [List.foldl_cons]
    rw [foldl_append_eq L (acc ++ b), foldl_append_eq L (ByteArray.empty ++ b)]
    simp [ByteArray.append_assoc]

lemma extract_append_left' (B C : ByteArray) : (B ++ C).extract 0 B.size = B := by
  apply ByteArray.ext
  simp [Array.extract_append]

/-- Element `j` of a concatenation, at the sum of the sizes before it. -/
theorem extract_foldl_append : ∀ (L : List ByteArray) (j : ℕ) (hj : j < L.length),
    (L.foldl (· ++ ·) ByteArray.empty).extract ((L.take j).map (·.size)).sum
      (((L.take j).map (·.size)).sum + L[j].size) = L[j]
  | [], _, hj => by simp at hj
  | b :: L, 0, _ => by
    rw [List.foldl_cons, foldl_append_eq]
    simpa using extract_append_left' _ _
  | b :: L, j + 1, hj => by
    rw [List.foldl_cons, foldl_append_eq]
    have h := extract_foldl_append L j (by simpa using hj)
    have hb : (ByteArray.empty ++ b).size = b.size := by simp
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.getElem_cons_succ]
    rw [Nat.add_assoc, ← hb, ByteArray.extract_append_size_add, h]

lemma zeros_size (n : ℕ) : (Prover.zeros n).size = n :=
  (rfl : (Prover.zeros n).size = (Array.replicate n (0 : UInt8)).size).trans
    (Array.size_replicate ..)

lemma fit_size (b : ByteArray) (n : ℕ) : (Prover.fit b n).size = n := by
  rw [Prover.fit, ByteArray.size_extract, ByteArray.size_append, zeros_size]; omega

lemma fit_of_size {b : ByteArray} {n : ℕ} (h : b.size = n) : Prover.fit b n = b := by
  subst h
  rw [Prover.fit, Nat.sub_self]
  apply ByteArray.ext
  rw [ByteArray.data_extract, ByteArray.data_append, Array.extract_append,
    show b.size = b.data.size from rfl]
  simp [Prover.zeros]

/-- Field `j` of an assembled proof, at the sum of the sizes before it. -/
lemma extract_assemble (p : Params) (f : Prover.Fields) (j : ℕ) (hj : j < 9) {a b : ℕ}
    (ha : a = (((Prover.fieldList p f).take j).map (·.size)).sum)
    (hb : b = a + ((Prover.fieldList p f)[j]'(by simp [Prover.fieldList]; omega)).size) :
    (Prover.assemble p f).extract a b =
      (Prover.fieldList p f)[j]'(by simp [Prover.fieldList]; omega) := by
  subst ha hb
  exact extract_foldl_append _ j _

/-- **The fields of an assembled proof** (`Prover.assemble`) are the fitted fields. -/
theorem fields_assemble (p : Params) (f : Prover.Fields) :
    let pf : Proof := { params := p, bytes := Prover.assemble p f }
    pf.corrections = Prover.fit f.corrections (16 * p.correctionBytes) ∧
    pf.cmult = Prover.fit f.cmult (p.nMask * p.nMultBytes) ∧
    pf.voleCheck = Prover.fit f.voleCheck 64 ∧
    pf.correction = Prover.fit f.correction p.witnessBytes ∧
    pf.qsProof = Prover.fit f.qsProof ((p.qsDegree - 1) * 16) ∧
    pf.opening = Prover.fit f.opening BAVC.openSize ∧
    pf.delta = Prover.fit f.delta 16 ∧
    pf.ivPre = Prover.fit f.ivPre 16 ∧
    pf.ctr = Prover.fit f.ctr 4 ∧
    pf.bytes.size = p.proofBytes := by
  intro pf
  simp only [pf, Proof.corrections, Proof.cmult, Proof.voleCheck, Proof.correction,
    Proof.qsProof, Proof.opening, Proof.delta, Proof.ivPre, Proof.ctr, Proof.field,
    Params.field?, Params.fieldSizes]
  simp only [List.forIn_cons, List.forIn_nil]
  simp only [String.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact extract_assemble p f 0 (by omega) (by simp [Prover.fieldList])
      (by simp [Prover.fieldList, fit_size])
  · exact extract_assemble p f 1 (by omega) (by simp [Prover.fieldList, fit_size])
      (by simp [Prover.fieldList, fit_size])
  · exact extract_assemble p f 2 (by omega) (by simp [Prover.fieldList, fit_size])
      (by simp [Prover.fieldList, fit_size])
  · exact extract_assemble p f 3 (by omega) (by simp [Prover.fieldList, fit_size]; omega)
      (by simp [Prover.fieldList, fit_size])
  · exact extract_assemble p f 4 (by omega) (by simp [Prover.fieldList, fit_size]; omega)
      (by simp [Prover.fieldList, fit_size])
  · exact extract_assemble p f 5 (by omega) (by simp [Prover.fieldList, fit_size]; omega)
      (by simp [Prover.fieldList, fit_size])
  · exact extract_assemble p f 6 (by omega) (by simp [Prover.fieldList, fit_size]; omega)
      (by simp [Prover.fieldList, fit_size])
  · exact extract_assemble p f 7 (by omega) (by simp [Prover.fieldList, fit_size]; omega)
      (by simp [Prover.fieldList, fit_size])
  · exact extract_assemble p f 8 (by omega) (by simp [Prover.fieldList, fit_size]; omega)
      (by simp [Prover.fieldList, fit_size])
  · rw [Prover.assemble, foldl_append_eq]
    simp [Prover.fieldList, fit_size, Params.proofBytes, Params.fieldSizes]
    ring

/-! ## The VOLE correlation of the prover's output -/

lemma zb_inj {x y : Bool} (h : zb x = zb y) : x = y := by
  cases x <;> cases y <;> simp_all [zb]

lemma correctionBytes_mul (p : Params) : 8 * p.correctionBytes = p.correctionRows := by
  simp only [Params.correctionBytes, Params.correctionRows, Params.witnessBits]; split <;> omega

lemma smallVoleUWords_spec (p : Params) (iv : ByteArray) (i : ℕ) (key : ℕ → ByteArray) {r : ℕ}
    (hr : r / 64 < p.colBytes / 8) :
    (Prover.smallVoleUWords p iv i key).size = p.colBytes / 8 ∧
      zb (wbit (Prover.smallVoleUWords p iv i key) r) =
        ∑ j ∈ range (2 ^ BAVC.kOf i), zb (wbit (prgWords p iv i (key j)) r) := by
  have h := foldl_xor_bit (fun _ => true) (fun j => prgWords p iv i (key j)) (r := r)
    (List.range (2 ^ BAVC.kOf i)) (zeroCol p) (by simpa [zeroCol] using hr)
  simp only [ite_true, Bool.true_and] at h
  refine ⟨h.1.trans (by simp [zeroCol]), ?_⟩
  rw [Prover.smallVoleUWords, h.2, wbit_zeroCol, list_sum_range]
  simp [zb]

/-- The prover's inputs `u^{(i)}` (`Prover.voleGen`). -/
def proverU (p : Params) (iv : ByteArray) (key : ℕ → ℕ → ByteArray) (i : ℕ) : Array UInt64 :=
  Prover.smallVoleUWords p iv i (key i)

/-- The prover's corrections `c_i = u^{(0)} ⊕ u^{(i)}` (`Prover.voleGen`; `c_0` is never read). -/
def proverCorr (p : Params) (iv : ByteArray) (key : ℕ → ℕ → ByteArray) (i : ℕ) : ByteArray :=
  Prover.correctionOf p (proverU p iv key 0) (proverU p iv key i)

/-- The corrected small-VOLE value `u^{(i)} = c_i + Σ_j R_j` (`smallVoleU`) of the prover's output
is `u = u^{(0)}` on the corrected rows. -/
theorem smallVoleU_prover (p : Params) (iv : ByteArray) (key : ℕ → ℕ → ByteArray) (i : ℕ)
    {r : ℕ} (hr : r < p.correctionRows) :
    smallVoleU p iv i (proverCorr p iv key i) (key i) r = zb (wbit (proverU p iv key 0) r) := by
  have hr64 : r / 64 < p.colBytes / 8 := by have := correctionRows_lt p; omega
  obtain ⟨hs0, h0⟩ := smallVoleUWords_spec p iv 0 (key 0) hr64
  obtain ⟨hsi, hi⟩ := smallVoleUWords_spec p iv i (key i) hr64
  rw [smallVoleU, ← hi]
  unfold proverU at *
  by_cases hi0 : i = 0
  · subst hi0
    simp [corrWords, wbit_zeroCol, zb]
  · have hcb : 8 * p.correctionBytes = p.correctionRows := correctionBytes_mul p
    have hcol : p.correctionBytes ≤ p.colBytes := by have := correctionRows_lt p; omega
    have hW : (xorWords (Prover.smallVoleUWords p iv 0 (key 0))
        (Prover.smallVoleUWords p iv i (key i))).size = p.colBytes / 8 := by
      rw [xorWords_size, hs0]
    have h8 : 8 ∣ p.colBytes := ⟨2 * p.voleColBlocks, by simp [Params.colBytes]; ring⟩
    have hsz : (Prover.correctionOf p (Prover.smallVoleUWords p iv 0 (key 0))
        (Prover.smallVoleUWords p iv i (key i))).size = p.correctionBytes := by
      rw [Prover.correctionOf, ByteArray.size_extract, bytesOfWords_size, hW]; omega
    have hbit : wbit (corrWords p i (proverCorr p iv key i)) r =
        (wbit (Prover.smallVoleUWords p iv 0 (key 0)) r ^^
          wbit (Prover.smallVoleUWords p iv i (key i)) r) := by
      simp only [corrWords, hi0, beq_iff_eq, ite_false, proverCorr, proverU]
      rw [Prover.correctionOf] at hsz ⊢
      have hZ : ∀ m, ({ data := Array.replicate m 0 } : ByteArray).size = m := fun m => by
        simp [ByteArray.size]
      rw [wbit_wordsOf_bytesOfWords _ _ _ (by rw [hW]; omega) (by omega)
        (by simp only [hZ, hsz]; omega), wbit_xorWords _ _ (by rw [hs0]; exact hr64)]
    rw [hbit, zb_xor]
    ring_nf
    simp [show (2 : ZMod 2) = 0 from rfl]

/-- **The prover's VOLE correlation, column by column**: for every `Δ` (bits `dbit`), the
verifier's key column `p_i + b` computed from the prover's corrections and leaf keys is the
prover's tag column plus `Δ_{p_i+b} · u` on the corrected rows. -/
theorem prover_column (p : Params) (iv : ByteArray) (key : ℕ → ℕ → ByteArray) (dbit : ℕ → Bool)
    {i b r : ℕ} (hi : i < BAVC.tau) (hb : b < BAVC.kOf i) (hr : r < p.correctionRows) :
    wbit (convertToVoleAt p dbit (proverCorr p iv key) iv key)[BAVC.bitOffset i + b]! r =
      (wbit (Prover.senderColumns p iv key)[BAVC.bitOffset i + b]! r ^^
        (dbit (BAVC.bitOffset i + b) && wbit (proverU p iv key 0) r)) := by
  have hr' := lt_of_lt_of_le hr (correctionRows_lt p)
  apply zb_inj
  rw [convertToVoleAt_col _ _ _ _ _ hi hb, Prover.senderColumns,
    convertToVoleAt_col _ _ _ _ _ hi hb,
    zb_xor, zb_and, treeColumns_affine _ _ _ _ _ _ hb hr', treeColumns_affine _ _ _ _ _ _ hb hr',
    testBit_hiddenIndex _ _ hb, testBit_hiddenIndex _ _ hb, smallVoleU_prover _ _ _ _ hr]
  simp [zb]

lemma ite_bool_xor_and (v d u : Bool) (L : GF128) :
    (if (v ^^ (d && u)) then L else 0) =
      (if v then L else 0) + (if u then 1 else 0) * (if d then L else 0) := by
  cases v <;> cases d <;> cases u <;> simp [CharTwo.add_self_eq_zero]

/-- **The prover's VOLE correlation on the lifted rows**: for every `Δ`, the verifier's CRT-lifted
row `r < ℓ'` (computed from the prover's corrections and leaf keys) is the prover's lifted tag
`v_r` (`Prover.voleGen`'s `vRows`: the rows of `crtReconstructWith` at `Δ = 0`) plus `u_r · Δ'`,
`Δ'` the lifted `Δ`. -/
theorem prover_row (h5 : ByteArray → ByteArray) (h0 : Array UInt32) (p : Params) (dbit : ℕ → Bool)
    (cmult cmult' : ByteArray) (T : CrtTables) (iv : ByteArray) (key : ℕ → ℕ → ByteArray) {r : ℕ}
    (hr : r < p.correctionRows) :
    (crtReconstructAt h5 p dbit cmult T iv
        (convertToVoleAt p dbit (proverCorr p iv key) iv key)).rows[r]!.toGF =
      (crtReconstructWith h0 p (fun _ => false) cmult' T
          (Prover.senderColumns p iv key)).rows[r]!.toGF +
        (if wbit (proverU p iv key 0) r then 1 else 0) * (W128.rowMul dbit 120 T.wCrt).toGF := by
  have hw : (crtReconstructWith h0 p (fun _ => false) cmult' T
      (Prover.senderColumns p iv key)).rows[r]!.toGF =
      ∑ c ∈ range 120, if wbit (Prover.senderColumns p iv key)[c]! r then liftCol T c else 0 := by
    simp only [crtReconstructWith]
    rw [getElem!_range_map _ _ hr, rowMul_toGF]
    rfl
  rw [rows_toGF _ _ _ _ _ _ _ hr, hw, rowMul_toGF, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c hc => ?_
  obtain ⟨hi, hle, hb⟩ := treeOf_spec (Finset.mem_range.1 hc)
  have hcc : c = BAVC.bitOffset (BAVC.treeOf c) + (c - BAVC.bitOffset (BAVC.treeOf c)) := by omega
  rw [hcc, prover_column p iv key dbit hi hb hr, ite_bool_xor_and]
  rfl

/-! ## QuickSilver -/

/-- `Σ_i a_i X^i`. -/
def polyOf (a : Array GF128) : GF128[X] := ∑ i ∈ range a.size, C (a.toList.getD i 0) * X ^ i

lemma foldr_horner (x : GF128) :
    ∀ l : List GF128,
      l.foldr (fun c acc => acc * x + c) 0 = ∑ i ∈ range l.length, l.getD i 0 * x ^ i
  | [] => by simp
  | c :: l => by
    rw [List.foldr_cons, foldr_horner x l, List.length_cons, Finset.sum_range_succ', Finset.sum_mul]
    simp [pow_succ, mul_assoc]

lemma evalPoly_eq (a : Array GF128) (x : GF128) : Prover.evalPoly a x = (polyOf a).eval x := by
  rw [Prover.evalPoly, ← Array.foldr_toList, foldr_horner, polyOf, eval_finsetSum]
  simp

lemma polyOf_degree_lt (a : Array GF128) : (polyOf a).degree < a.size := by
  rw [polyOf]
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  rcases Nat.eq_zero_or_pos a.size with h | h
  · simp [h]
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun i hi => ?_
  refine lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) ?_
  exact_mod_cast Finset.mem_range.1 hi

lemma samplePt_ne_zero {k : ℕ} (hk : k + 1 < 2 ^ 64) : Prover.samplePt k ≠ 0 := by
  intro h
  have := congrArg GF128.lo h
  simp only [Prover.samplePt] at this
  have h2 := congrArg UInt64.toNat this
  rw [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hk] at h2
  exact absurd h2 (by rw [show (0 : GF128).lo = 0 from rfl]; simp)

lemma samplePt_injOn (n : ℕ) (hn : n < 2 ^ 64) :
    Set.InjOn Prover.samplePt (Finset.range n : Set ℕ) := by
  intro a ha b hb h
  simp only [coe_range, Set.mem_Iio] at ha hb
  have := congrArg (fun z => z.lo.toNat) h
  simp only [Prover.samplePt, Nat.toUInt64, UInt64.toNat_ofNat'] at this
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  omega

lemma gfId_apply (a : GF128) : gfId.toFun a = a := rfl

/-- The witness MACs at `Δ' = X` as polynomials: `v_j + w_j X` for `j < ℓ`, zero above. -/
def keyPoly (p : Params) (vRows : Array W128) (w : ByteArray) (j : ℕ) : GF128[X] :=
  if j < p.witnessBits then C vRows[j]!.toGF + C (if Prover.bitOf w j then 1 else 0) * X else 0

lemma keyPoly_eval (p : Params) (vRows : Array W128) (w : ByteArray) (x : GF128) (j : ℕ) :
    (keyPoly p vRows w j).eval x = (Prover.qsKeys p vRows w x).getD j 0 := by
  unfold keyPoly Prover.qsKeys
  by_cases hj : j < p.witnessBits
  · simp only [hj, ↓reduceIte, Array.getD_eq_getD_getElem?, Array.getElem?_map,
      Array.getElem?_range, Option.map_some, Option.getD_some]
    split <;> simp
  · simp [hj, Array.getD_eq_getD_getElem?]

lemma keyPoly_deg (p : Params) (vRows : Array W128) (w : ByteArray) (j : ℕ) :
    (keyPoly p vRows w j).natDegree ≤ 1 ∧
      (keyPoly p vRows w j).coeff 1 = if j < p.witnessBits ∧ Prover.bitOf w j then 1 else 0 := by
  unfold keyPoly
  by_cases hj : j < p.witnessBits
  · simp only [hj, ↓reduceIte, true_and]
    refine ⟨(natDegree_add_le _ _).trans (max_le (by simp)
      (by simpa using
        natDegree_C_mul_X_pow_le (if Prover.bitOf w j then (1 : GF128) else 0) 1)), ?_⟩
    split_ifs <;> simp
  · simp [hj]

/-- **The verifier's QuickSilver value at the prover's keys and masks.** For `Δ' = x ≠ 0`, with
the witness keys `v_j + w_j x` and masks `ṽ_mask + u_mask x` (`Prover.qsAt`), the check value of any
proof `pf` is `EndToEnd`'s check polynomial (the system's circuits on the affine witness MACs, the
remainder `maskPoly d ṽ_mask u_mask ã 0`, `ã` read from `pf`) at `x`. -/
theorem qsAt_eq (pf : Proof) (c2 : ByteArray) (values : (ℕ → GF128) → List GF128)
    (vRows vMask uMask : Array W128) (w : ByteArray) (cs : System GF128)
    (hvals : ∀ x, values x = cs.values x) (hdeg : ∀ e ∈ cs, e.degree ≤ pf.params.qsDegree)
    {x : GF128} (hx : x ≠ 0) :
    Prover.qsAt pf c2 values vRows vMask uMask w x =
      (sysCheckPoly (keyPoly pf.params vRows w) cs pf.params.qsDegree
        (Seed.zkCoeff cs.length (gfOfBytes c2 0) (gfOfBytes c2 16) (gfOfBytes c2 32)
          ⟨W128.word c2 48, 0⟩)
        (Seed.maskPoly pf.params.qsDegree (fun i => vMask[i]!.toGF) (fun i => uMask[i]!.toGF)
          (fun i => gfOfBytes pf.qsProof (16 * (i - 1))) 0)).eval x := by
  rw [eval_sysCheckPoly]
  have hk := map_constraintKeys gfId GF128.card_eq pf.params (Prover.qsKeys pf.params vRows w x) x
    values cs (fun y => (List.map_id _).trans (hvals y))
  have hcs : (constraintKeys pf.params (Prover.qsKeys pf.params vRows w x) x values).map gfId =
      List.ofFn fun k => mac (fun j => (keyPoly pf.params vRows w j).eval x) (gfId x)
        (sysQS cs pf.params.qsDegree k) := by
    rw [hk]
    congr 1
    funext k
    simp only [gfId_apply]
    rw [keyVals, sysQS, mac_constraintQS _ hx _ (hdeg _ (List.get_mem cs k))]
    simp only [keyPoly_eval]
  have h := map_qsCheck gfId pf c2 _ (Prover.qsMasks pf.params vMask uMask x) x cs _ hcs
    (fun i => vMask[i]!.toGF) (fun i => uMask[i]!.toGF) (fun i hi => by
      have hi' : i < pf.params.nMask := by simp only [Params.nMask]; omega
      simp [Prover.qsMasks, hi', getElem!_pos, Prover.W128.ofGF, W128.toGF]
      rfl) 0
  rw [add_zero] at h
  exact h

lemma maskPoly_eval_sub (d : ℕ) (a b ã ã' : ℕ → GF128) (x : GF128) :
    (Seed.maskPoly d a b ã 0).eval x =
      (Seed.maskPoly d a b ã' 0).eval x + ∑ i ∈ Ico 1 d, (ã i + ã' i) * x ^ i := by
  simp only [Seed.maskPoly, eval_add, eval_finsetSum, eval_mul, eval_C, eval_X, eval_pow, add_zero,
    add_mul, Finset.sum_add_distrib]
  have h : ∀ y : GF128, y + y = 0 := fun y => CharTwo.add_self_eq_zero y
  linear_combination -h (∑ i ∈ Ico 1 d, ã' i * x ^ i)

lemma getElem!_eq_getD (g : Array GF128) {i : ℕ} (hi : i < g.size) : g[i]! = g.toList.getD i 0 := by
  simp [getElem!_pos, hi, List.getD_eq_getElem?_getD]

/-- **QuickSilver completeness.** If `Prover.qsProve` returns `(qs_check, ã)` (with `pf0`'s `ã`
zero), then for every `Δ' = x ≠ 0` the verifier's check value at the prover's keys and masks, on
any proof `pf` that carries this `ã`, is `qs_check`: the prover's coefficients make the check value
independent of `Δ'`. Assumed: the statement's evaluator is the system `cs` of degree `≤ d`
(`Bridge/Relations.lean` proves this for the five relations), `1 ≤ d < 2⁶⁴ − 1`. The witness need
not be known to satisfy `cs`: `qsProve` checks the top coefficient. -/
theorem qsProve_complete (pf0 : Proof) (c2 : ByteArray) (values : (ℕ → GF128) → List GF128)
    (vRows vMask uMask : Array W128) (w : ByteArray) {check : GF128} {aT : Array GF128}
    (h : Prover.qsProve pf0 c2 values vRows vMask uMask w = .ok (check, aT))
    (cs : System GF128) (hvals : ∀ x, values x = cs.values x)
    (hdeg : ∀ e ∈ cs, e.degree ≤ pf0.params.qsDegree) (hd : 1 ≤ pf0.params.qsDegree)
    (hd' : pf0.params.qsDegree + 1 < 2 ^ 64) (h0 : ∀ i, gfOfBytes pf0.qsProof (16 * i) = 0)
    (pf : Proof) (hp : pf.params = pf0.params) (hqs : pf.qsProof = Prover.gfsToBytes aT)
    {x : GF128} (hx : x ≠ 0) :
    Prover.qsAt pf c2 values vRows vMask uMask w x = check := by
  -- Unpack the prover's run.
  unfold Prover.qsProve at h
  set d := pf0.params.qsDegree with hdd
  set xs := (Array.range (d + 1)).map Prover.samplePt
  set ys := xs.map (Prover.qsAt pf0 c2 values vRows vMask uMask w)
  set g := Prover.interpolate xs ys
  dsimp only at h
  split_ifs at h with hsz hgd hall
  all_goals first | (cases h; done) | skip
  rename_i hgd hall
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨hcheck, haT⟩ := h
  simp only [bne_iff_ne, ne_eq, not_not, Bool.not_eq_true', Bool.not_eq_false] at hsz hgd hall
  change g.size = d + 1 at hsz
  change g[d]! = 0 at hgd
  change g[0]! = check at hcheck
  change (Array.range (d - 1)).map (fun i => g[i + 1]!) = aT at haT
  have hgd' := hgd
  -- `G = P₀` on the nonzero points, with `P₀` of degree `≤ d`.
  set χ := Seed.zkCoeff cs.length (gfOfBytes c2 0) (gfOfBytes c2 16) (gfOfBytes c2 32)
    (⟨W128.word c2 48, 0⟩ : GF128)
  set P0 := sysCheckPoly (keyPoly pf0.params vRows w) cs d χ
    (Seed.maskPoly d (fun i => vMask[i]!.toGF) (fun i => uMask[i]!.toGF)
      (fun i => gfOfBytes pf0.qsProof (16 * (i - 1))) 0)
  have hG : ∀ y ≠ 0, Prover.qsAt pf0 c2 values vRows vMask uMask w y = P0.eval y :=
    fun y hy => qsAt_eq pf0 c2 values vRows vMask uMask w cs hvals hdeg hy
  have hP0 : P0.natDegree ≤ d :=
    (sysCheckPoly_natDegree_coeff hd cs hdeg (keyPoly pf0.params vRows w)
      (fun j => (keyPoly pf0.params vRows w j).coeff 1)
      (fun j => ⟨(keyPoly_deg _ _ _ j).1, rfl⟩) χ _ (Seed.maskPoly_natDegree_le _ _ _ _ _)).1
  have hpoly : polyOf g = P0 := by
    refine eq_of_degrees_lt_of_eval_index_eq (range (d + 1)) (samplePt_injOn (d + 1) hd')
      ?_ ?_ fun k hk => ?_
    · simpa [hsz] using polyOf_degree_lt g
    · rw [card_range]
      exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hP0)
    · have hk' := Finset.mem_range.1 hk
      have := List.all_eq_true.1 hall k (List.mem_range.2 hk')
      simp only [beq_iff_eq] at this
      have hx' : xs[k]! = Prover.samplePt k := by simp [xs, getElem!_pos, hk']
      have hy' : ys[k]! = Prover.qsAt pf0 c2 values vRows vMask uMask w (Prover.samplePt k) := by
        simp [ys, xs, getElem!_pos, hk']
      rw [← evalPoly_eq, ← hx', this, hy', hx', hG _ (samplePt_ne_zero (by omega))]
  -- The verifier's value on `pf`.
  have hpf := qsAt_eq pf c2 values vRows vMask uMask w cs hvals (hp ▸ hdeg) hx
  have hP := eval_sysCheckPoly (keyPoly pf.params vRows w) cs pf.params.qsDegree
  have hP0e := eval_sysCheckPoly (keyPoly pf0.params vRows w) cs d χ
    (Seed.maskPoly d (fun i => vMask[i]!.toGF) (fun i => uMask[i]!.toGF)
      (fun i => gfOfBytes pf0.qsProof (16 * (i - 1))) 0) x
  rw [hpf, hP, hp, maskPoly_eval_sub _ _ _ _ (fun i => gfOfBytes pf0.qsProof (16 * (i - 1))),
    ← add_assoc, ← hdd, ← hP0e]
  change P0.eval x + _ = check
  rw [← hpoly, polyOf]
  simp only [h0, add_zero]
  -- `Σ_{i ≤ d} g_i x^i + Σ_{1 ≤ i < d} g_i x^i = g_0`.
  have hã : ∀ i ∈ Ico 1 d, gfOfBytes pf.qsProof (16 * (i - 1)) * x ^ i =
      g.toList.getD i 0 * x ^ i := by
    intro i hi
    have hi := Finset.mem_Ico.1 hi
    rw [hqs, gfOfBytes_gfsToBytes _ (by rw [← haT]; simp; omega), ← haT,
      getElem!_range_map _ _ (by omega), Nat.sub_add_cancel hi.1, getElem!_eq_getD _ (by omega)]
  rw [Finset.sum_congr rfl hã, eval_finsetSum, hsz, Finset.sum_range_succ,
    Finset.sum_range_eq_add_Ico _ (by omega : 0 < d)]
  simp only [eval_mul, eval_C, eval_pow, eval_X, pow_zero, mul_one]
  rw [← getElem!_eq_getD _ (by omega : d < g.size), hgd',
    ← getElem!_eq_getD _ (by omega : 0 < g.size),
    ← hcheck]
  have h2 : ∀ y : GF128, y + y = 0 := fun y => CharTwo.add_self_eq_zero y
  linear_combination h2 (∑ i ∈ Ico 1 d, g.toList.getD i 0 * x ^ i)

/-! ## The VOLE check -/

lemma foldl_horner_lin (key Δ : GF128) :
    ∀ (a b : List GF128) (sa sb : GF128), a.length = b.length →
      (List.zipWith (fun x y => x + Δ * y) a b).foldl (fun s x => s * key + x) (sa + Δ * sb) =
        a.foldl (fun s x => s * key + x) sa + Δ * b.foldl (fun s x => s * key + x) sb
  | [], [], _, _, _ => rfl
  | x :: a, y :: b, sa, sb, h => by
    simp only [List.zipWith_cons_cons, List.foldl_cons]
    rw [show (sa + Δ * sb) * key + (x + Δ * y) = (sa * key + x) + Δ * (sb * key + y) by ring]
    exact foldl_horner_lin key Δ a b _ _ (by simpa using h)
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h

/-- `horner` is linear: if `c = a + Δ b` elementwise, `horner c = horner a + Δ horner b`. -/
theorem horner_lin (key Δ : GF128) (a b c : Array GF128) (hab : a.size = b.size)
    (hc : c.toList = List.zipWith (fun x y => x + Δ * y) a.toList b.toList) :
    horner key c = horner key a + Δ * horner key b := by
  simp only [horner, ← Array.foldl_toList, hc]
  have := foldl_horner_lin key Δ a.toList b.toList 0 0 (by simpa using hab)
  simpa using this

/-- The hashed rows `rows ‖ q_mask[0 .. d − 1)` of the VOLE check, as a list. -/
lemma hashed_toList (p : Params) (rows qMask : Array W128) :
    (rows.map (·.toGF) ++ (qMask.extract 0 (p.qsDegree - 1)).map (·.toGF)).toList =
      rows.toList.map (·.toGF) ++ (qMask.toList.take (p.qsDegree - 1)).map (·.toGF) := by
  simp [Array.toList_extract, List.extract]

lemma voleHashReceiver_size (p : Params) (c1 : ByteArray) (rows qMask : Array W128) (dl : GF128)
    (ut : ByteArray) : (voleHashReceiver p c1 rows qMask dl ut).size = 4 := by
  simp only [voleHashReceiver, Id.run]
  exact (Array.size_map ..).trans (Array.size_range ..)

/-- The four outputs of `voleHashReceiver`. -/
lemma voleHashReceiver_get (p : Params) (c1 : ByteArray) (rows qMask : Array W128) (dl : GF128)
    (ut : ByteArray) (i : Fin 4) :
    (voleHashReceiver p c1 rows qMask dl ut)[(i : ℕ)]! =
      qMask[p.qsDegree - 1 + i]!.toGF +
        horner (![gfOfBytes c1 80, gfOfBytes c1 96, gfOfBytes c1 112, ⟨W128.word c1 128, 0⟩] i)
          (rows.map (·.toGF) ++ (qMask.extract 0 (p.qsDegree - 1)).map (·.toGF)) +
        horner (gfOfBytes c1 64)
            (rows.map (·.toGF) ++ (qMask.extract 0 (p.qsDegree - 1)).map (·.toGF)) *
          gfOfBytes c1 (16 * i) + dl * gfOfBytes ut (16 * i) := by
  fin_cases i <;> simp [voleHashReceiver]

/-- **The VOLE check of the prover's output.** If the verifier's lifted rows and masks are
`v + u·Δ'` (the VOLE correlation: `prover_row` for the rows; the masks are the CRT VOLE's), then
its VOLEHash `h`, corrected by `Δ'·ũ` with the prover's `ũ` (`Prover.voleGen`: the VOLEHash of
`u`, written with `gfsToBytes`), is the prover's `h_V` (the VOLEHash of `v`), so the verifier
recomputes the prover's `chal2`. -/
theorem voleHash_complete (p : Params) (c1 : ByteArray) (vRows vMask uMask rowsQ maskQ : Array W128)
    (u : Array UInt64) (Δ : GF128) (z z' : ByteArray)
    (hrs : rowsQ.size = p.correctionRows) (hvs : vRows.size = p.correctionRows)
    (hmq : maskQ.size = p.nMask) (hmv : vMask.size = p.nMask) (hmu : uMask.size = p.nMask)
    (hrows : ∀ r < p.correctionRows,
      rowsQ[r]!.toGF = vRows[r]!.toGF + (if wbit u r then 1 else 0) * Δ)
    (hmask : ∀ m < p.nMask, maskQ[m]!.toGF = vMask[m]!.toGF + uMask[m]!.toGF * Δ) :
    voleHashReceiver p c1 rowsQ maskQ Δ (Prover.gfsToBytes (voleHashReceiver p c1
      ((Array.range p.correctionRows).map fun r => if wbit u r then (⟨1, 0⟩ : W128) else W128.zero)
      uMask 0 z)) = voleHashReceiver p c1 vRows vMask 0 z' := by
  set uRows := (Array.range p.correctionRows).map fun r =>
    if wbit u r then (⟨1, 0⟩ : W128) else W128.zero
  set d := p.qsDegree
  have hnm : d - 1 + 4 ≤ p.nMask := by simp only [Params.nMask, d]; omega
  -- The hashed rows are `v + Δ u` elementwise.
  have hxs : (rowsQ.map (·.toGF) ++ (maskQ.extract 0 (d - 1)).map (·.toGF)).toList =
      List.zipWith (fun x y => x + Δ * y)
        (vRows.map (·.toGF) ++ (vMask.extract 0 (d - 1)).map (·.toGF)).toList
        (uRows.map (·.toGF) ++ (uMask.extract 0 (d - 1)).map (·.toGF)).toList := by
    rw [hashed_toList, hashed_toList, hashed_toList]
    apply List.ext_getElem
    · simp [hrs, hvs, hmq, hmv, hmu, uRows]
    intro k h1 h2
    simp only [List.getElem_zipWith]
    by_cases hk : k < p.correctionRows
    · have e := hrows k hk
      rw [getElem!_pos rowsQ k (by omega), getElem!_pos vRows k (by omega)] at e
      simp only [List.getElem_append, List.length_map, Array.length_toList, hrs, hvs, uRows,
        Array.size_map, Array.size_range, hk, ↓reduceDIte, List.getElem_map, Array.getElem_toList,
        Array.getElem_map, Array.getElem_range]
      rw [e]
      by_cases hb : wbit u k
      · simp only [hb, ↓reduceIte]; rw [show W128.toGF ⟨1, 0⟩ = 1 from rfl]; ring
      · simp only [hb, Bool.false_eq_true, ↓reduceIte]; rw [show W128.toGF W128.zero = 0 from rfl]
        ring
    · have hk1 : k - p.correctionRows < d - 1 := by
        simp [hrs, hmq] at h1; omega
      have e := hmask (k - p.correctionRows) (by omega)
      rw [getElem!_pos maskQ _ (by omega), getElem!_pos vMask _ (by omega),
        getElem!_pos uMask _ (by omega)] at e
      simp only [List.getElem_append, List.length_map, Array.length_toList, hrs, hvs, uRows,
        Array.size_map, Array.size_range, hk, ↓reduceDIte, List.getElem_map, List.getElem_take,
        Array.getElem_toList]
      rw [e]
      ring
  have hab : (vRows.map (·.toGF) ++ (vMask.extract 0 (d - 1)).map (·.toGF)).size =
      (uRows.map (·.toGF) ++ (uMask.extract 0 (d - 1)).map (·.toGF)).size := by
    simp [hvs, hmv, hmu, uRows]
  have hU : ∀ i < 4,
      gfOfBytes (Prover.gfsToBytes (voleHashReceiver p c1 uRows uMask 0 z)) (16 * i) =
      (voleHashReceiver p c1 uRows uMask 0 z)[i]! := fun i hi =>
    gfOfBytes_gfsToBytes _ (by rw [voleHashReceiver_size]; exact hi)
  apply Array.ext
  · rw [voleHashReceiver_size, voleHashReceiver_size]
  intro i h1 h2
  have hi : i < 4 := by rwa [voleHashReceiver_size] at h1
  rw [← getElem!_pos _ i h1, ← getElem!_pos _ i h2]
  obtain ⟨i, rfl⟩ : ∃ j : Fin 4, (j : ℕ) = i := ⟨⟨i, hi⟩, rfl⟩
  rw [voleHashReceiver_get, voleHashReceiver_get, hU i i.isLt, voleHashReceiver_get,
    horner_lin _ Δ _ _ _ hab hxs, horner_lin _ Δ _ _ _ hab hxs, hmask _ (by omega)]
  have h2 : ∀ y : GF128, y + y = 0 := fun y => CharTwo.add_self_eq_zero y
  linear_combination Δ * h2 (uMask[d - 1 + ↑i]!.toGF +
    horner (![gfOfBytes c1 80, gfOfBytes c1 96, gfOfBytes c1 112, ⟨W128.word c1 128, 0⟩] i)
      (uRows.map (·.toGF) ++ (uMask.extract 0 (d - 1)).map (·.toGF)) +
    horner (gfOfBytes c1 64) (uRows.map (·.toGF) ++ (uMask.extract 0 (d - 1)).map (·.toGF)) *
      gfOfBytes c1 (16 * ↑i))

/-! ## Inverting the prover's run -/

lemma u8_bit (x : UInt8) (s : ℕ) (hs : s < 8) :
    ((x >>> s.toUInt8) &&& 1 == 1) = x.toNat.testBit s := by
  have h1 : ((x >>> s.toUInt8) &&& 1).toNat = x.toNat / 2 ^ s % 2 := by
    rw [UInt8.toNat_and, UInt8.toNat_shiftRight]
    simp [Nat.mod_eq_of_lt hs, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod,
      Nat.mod_eq_of_lt (show s < 256 by omega)]
  have key : ∀ y : UInt8, (y == 1) = decide (y.toNat = 1) := fun y => by
    by_cases hy : y = 1
    · subst hy; rfl
    · rw [beq_false_of_ne hy]
      exact (decide_eq_false fun h => hy (UInt8.toNat_inj.1 (h.trans rfl))).symm
  rw [Nat.testBit_eq_decide_div_mod_eq, key, h1]

lemma findFirst_some {α : Type} (f : ℕ → Option α) :
    ∀ (n c : ℕ) {a : α}, Prover.findFirst f n c = some a → ∃ k, f k = some a
  | 0, _, _, h => by simp [Prover.findFirst] at h
  | n + 1, c, a, h => by
    simp only [Prover.findFirst] at h
    split at h
    · rename_i b hb; cases h; exact ⟨c, hb⟩
    · exact findFirst_some f n (c + 1) h

lemma grindStep_some {Hs : Hashes} {s : Prover.Pending} {pre : ByteArray} {k ctr : ℕ}
    {delta o : ByteArray} (h : Prover.grindStep Hs s pre k = some (ctr, delta, o)) :
    ctr = k ∧ delta = Hs.hash .h23 ((AES.pushLE32 pre k.toUInt32).push 11) ∧ delta.get! 15 = 0 ∧
      BAVC.openAt s.tree s.leaves.coms delta = some o := by
  unfold Prover.grindStep at h
  dsimp only at h
  split_ifs at h with h15
  · obtain ⟨o', ho', he⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact ⟨rfl, rfl, by simpa using h15, ho'⟩

/-- **What a successful `proveCommit` computed.** -/
lemma proveCommit_inv {Hs : Hashes} {st : Statement} {wSuffix : ByteArray} {s : Prover.Pending}
    {proof : ByteArray} (h : Prover.proveCommit Hs st wSuffix s = .ok proof) :
    let p := s.params
    let w := s.wPrefix ++ wSuffix
    let ub := bytesOfWords s.u
    let correction : ByteArray :=
      ⟨(Array.range p.witnessBytes).map fun k => ub.get! k ^^^ w.get! k⟩
    let f1 := { s.fields with correction := correction }
    let pf1 : Proof := { params := p, bytes := Prover.assemble p f1 }
    let c2 := chal2 Hs pf1 s.chal1 s.hV (st.muDelayed Hs s.chal1) st.binder2
    let values := st.values s.chal1 (st.combBytes Hs c2)
    w.size = p.witnessBytes ∧ ∃ check aT ctr delta opening,
      Prover.qsProve pf1 c2 values s.vRows s.vMask s.uMask w = .ok (check, aT) ∧
      Prover.findFirst (Prover.grindStep Hs s (c2 ++ gfToBytes check ++ Prover.gfsToBytes aT))
        (2 ^ 32) 0 = some (ctr, delta, opening) ∧
      proof = Prover.assemble p
        { f1 with qsProof := Prover.gfsToBytes aT, opening := opening, delta := delta,
                  ctr := AES.pushLE32 ByteArray.empty ctr.toUInt32 } := by
  intro p w ub correction f1 pf1 c2 values
  unfold Prover.proveCommit at h
  dsimp only at h
  split_ifs at h with hw
  · cases h
  refine ⟨by simpa [w, p, ByteArray.size_append] using hw, ?_⟩
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  rename_i v hq
  obtain ⟨check, aT⟩ := v
  generalize hf : Prover.findFirst _ (2 ^ 32) 0 = r at h
  rcases r with _ | ⟨ctr, delta, opening⟩
  · cases h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact ⟨check, aT, ctr, delta, opening, hq, hf, h.symm⟩

/-! ## Sizes and bytes -/

/-- The output lengths of the hash record are the domains' (`Hashes.shake` has them). -/
def HashesWF (Hs : Hashes) : Prop := ∀ k x, (Hs.hash k x).size = k.outLen

lemma stateBytes_size (a : Array UInt64) (n : ℕ) : (Spec.SHAKE.stateBytes a n).size = n := by
  have h : ∀ (l : List ℕ) (o : ByteArray),
      (l.foldl (fun o i => o.push ((a.getD (i / 8) 0 >>> (8 * (i % 8)).toUInt64).toUInt8)) o).size =
        o.size + l.length := by
    intro l; induction l with
    | nil => simp
    | cons j l ih => intro o; rw [List.foldl_cons, ih]; simp; omega
  simp only [Spec.SHAKE.stateBytes, Id.run]
  rw [forIn_range_foldl _ _ _ (fun i (o : ByteArray) =>
    o.push ((a.getD (i / 8) 0 >>> (8 * (i % 8)).toUInt64).toUInt8)) fun _ _ => rfl]
  exact (h _ _).trans (by simp)

lemma squeeze_size (rate n : ℕ) (a0 : Array UInt64) (o0 : ByteArray) :
    (forIn (m := Id) [:n] (a0, o0) (fun _ (s : Array UInt64 × ByteArray) =>
      pure (ForInStep.yield
        (Spec.SHAKE.keccakF1600 s.1, s.2 ++ Spec.SHAKE.stateBytes s.1 rate)))).2.size =
      o0.size + n * rate := by
  rw [forIn_range_foldl _ _ _ (fun _ (s : Array UInt64 × ByteArray) =>
    (Spec.SHAKE.keccakF1600 s.1, s.2 ++ Spec.SHAKE.stateBytes s.1 rate)) fun _ _ => rfl]
  have h : ∀ (l : List ℕ) (s : Array UInt64 × ByteArray),
      (l.foldl (fun s _ =>
        (Spec.SHAKE.keccakF1600 s.1, s.2 ++ Spec.SHAKE.stateBytes s.1 rate)) s).2.size =
        s.2.size + l.length * rate := by
    intro l; induction l with
    | nil => simp
    | cons j l ih => intro s; rw [List.foldl_cons, ih]; simp [stateBytes_size]; ring
  exact (h _ _).trans (by simp)

theorem sponge_size (rate : Nat) (hr : 0 < rate) (ds : UInt8) (input : ByteArray) (outLen : Nat) :
    (Spec.SHAKE.sponge rate ds input outLen).size = outLen := by
  simp only [Spec.SHAKE.sponge, Id.run]
  show ByteArray.size (ByteArray.extract
    (forIn (m := Id) [:outLen / rate + 1] (_, ByteArray.empty) _).2 0 outLen) = outLen
  rw [ByteArray.size_extract, squeeze_size]
  have : outLen < (outLen / rate + 1) * rate := by
    rw [Nat.add_mul, one_mul]; exact Nat.lt_div_mul_add hr
  simp only [ByteArray.size_empty, zero_add]
  omega

/-- SHAKE128 in every domain has the domains' output lengths. -/
theorem hashesWF_shake : HashesWF Hashes.shake := fun _ _ => sponge_size 168 (by norm_num) _ _ _

lemma gfsToBytes_size (xs : Array GF128) : (Prover.gfsToBytes xs).size = 16 * xs.size := by
  rw [Prover.gfsToBytes, bytesOfWords_size]
  simp [List.length_flatMap, List.sum_replicate]; ring

lemma pushLE32_eq (b : ByteArray) (x : UInt32) :
    AES.pushLE32 b x = b ++ AES.pushLE32 ByteArray.empty x := by
  apply ByteArray.ext
  rw [← Array.toList_inj]
  simp [AES.pushLE32]

lemma pushLE32_size (x : UInt32) : (AES.pushLE32 ByteArray.empty x).size = 4 := by
  simp [AES.pushLE32]

/-- The prover's corrections, sliced as the verifier reads them (`Proof.correctionOf`). -/
lemma correctionOf_concat (p : Params) (c : ℕ → ByteArray)
    (hc : ∀ i, (c i).size = p.correctionBytes)
    {i : ℕ} (hi1 : 1 ≤ i) (hi : i < BAVC.tau) :
    let C := (List.range (BAVC.tau - 1)).foldl (fun acc j => acc ++ c (j + 1)) ByteArray.empty
    C.extract ((i - 1) * p.correctionBytes) (i * p.correctionBytes) = c i := by
  intro C
  have ht : BAVC.tau = 17 := rfl
  have hC :
      C = ((List.range (BAVC.tau - 1)).map fun j => c (j + 1)).foldl (· ++ ·) ByteArray.empty := by
    simp [C, List.foldl_map]
  have hx := extract_foldl_append ((List.range (BAVC.tau - 1)).map fun j => c (j + 1)) (i - 1)
    (by simp only [List.length_map, List.length_range]; omega)
  have hs : (((List.range (BAVC.tau - 1)).map fun j => c (j + 1)).take (i - 1)).map (·.size) =
      List.replicate (i - 1) p.correctionBytes := by
    apply List.ext_getElem
    · simp only [List.length_map, List.length_take, List.length_range, List.length_replicate]
      omega
    · intro k h1 h2; simp [hc]
  simp only [hs, List.sum_replicate, smul_eq_mul, List.getElem_map, List.getElem_range,
    Nat.sub_add_cancel hi1, hc] at hx
  rw [hC, show i * p.correctionBytes = (i - 1) * p.correctionBytes + p.correctionBytes by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hi1]]
  exact hx

lemma correctionOf_size (p : Params) (u0 ui : Array UInt64) (h0 : u0.size = p.colBytes / 8) :
    (Prover.correctionOf p u0 ui).size = p.correctionBytes := by
  have := correctionRows_lt p
  have := correctionBytes_mul p
  rw [Prover.correctionOf, ByteArray.size_extract, bytesOfWords_size, xorWords_size, h0]
  omega

/-- `convertToVoleAt` reads the corrections only for `1 ≤ i < τ`. -/
lemma convertToVoleAt_congr_corr (p : Params) (dbit : ℕ → Bool) (iv : ByteArray)
    (key : ℕ → ℕ → ByteArray) {corr corr' : ℕ → ByteArray}
    (h : ∀ i, 1 ≤ i → i < BAVC.tau → corr i = corr' i) :
    convertToVoleAt p dbit corr iv key = convertToVoleAt p dbit corr' iv key := by
  have ht : ∀ i ∈ Array.range BAVC.tau,
      treeColumns p iv i (BAVC.hiddenIndex dbit i) (corr i) (key i) =
      treeColumns p iv i (BAVC.hiddenIndex dbit i) (corr' i) (key i) := by
    intro i hi
    have hi := Array.mem_range.1 hi
    by_cases h0 : i = 0
    · subst h0; simp [treeColumns, corrWords]
    · rw [h i (by omega) hi]
  unfold convertToVoleAt
  rw [Array.map_congr_left ht]

/-- The verifier's corrected witness keys of the prover's proof: `q_j + d_j Δ' = v_j + w_j Δ'`. -/
lemma correctedKeys_prover (pf : Proof) (rows vRows : Array W128) (u : Array UInt64)
    (w : ByteArray) (Δ : GF128) (hu : pf.params.witnessBits ≤ 64 * u.size)
    (hrows : ∀ r < pf.params.witnessBits,
      rows[r]!.toGF = vRows[r]!.toGF + (if wbit u r then 1 else 0) * Δ)
    (hd : pf.correction =
      ⟨(Array.range pf.params.witnessBytes).map fun k => (bytesOfWords u).get! k ^^^ w.get! k⟩) :
    correctedKeys pf rows Δ = Prover.qsKeys pf.params vRows w Δ := by
  apply Array.ext
  · simp [correctedKeys, Prover.qsKeys]
  intro j h1 h2
  have hj : j < pf.params.witnessBits := by simpa [correctedKeys] using h1
  simp only [correctedKeys, Prover.qsKeys, Array.getElem_map, Array.getElem_range]
  have hjb : j / 8 < pf.params.witnessBytes := by simp only [Params.witnessBits] at hj; omega
  have hbit : ((pf.correction.get! (j / 8) >>> (j % 8).toUInt8) &&& 1 == 1) =
      (wbit u j ^^ Prover.bitOf w j) := by
    have hg : pf.correction.get! (j / 8) = (bytesOfWords u).get! (j / 8) ^^^ w.get! (j / 8) := by
      rw [hd, byteArray_get!_eq]
      simp [hjb]
    have hs : j % 8 < 8 := Nat.mod_lt _ (by norm_num)
    rw [hg, Prover.bitOf, u8_bit _ _ hs, u8_bit _ _ hs, UInt8.toNat_xor,
      Nat.testBit_xor, bytesOfWords_get _ (by omega),
      testBit_shiftRight_toUInt8 _ _ _ (by omega) hs, wbit_eq]
    have e : 8 * (j / 8 % 8) + j % 8 = j % 64 := by omega
    rw [show j / 8 / 8 = j / 64 by omega, e]
  rw [hbit, hrows j hj]
  by_cases hu' : wbit u j <;> by_cases hw' : Prover.bitOf w j <;>
    simp [hu', hw', CharTwo.add_self_eq_zero, add_assoc]

/-! ## What `voleGen` computes -/

section VoleGen

variable (Hs : Hashes) (T : CrtTables) (p : Params) (mu1 wPrefix rho binder1 : ByteArray)

/-- The proof written by step 1 before the VOLE check (`chal1` is computed on it). -/
def step1Proof (p : Params) (s : Prover.Pending) : Proof :=
  { params := p,
    bytes := Prover.assemble p { s.fields with voleCheck := .empty, correction := .empty } }

theorem voleGen_spec :
    let s := Prover.voleGen Hs T p mu1 wPrefix rho binder1
    let key := leafKey s.leaves
    s.params = p ∧ s.wPrefix = wPrefix ∧
    s.iv = Hs.hash .h4 ((s.ivPre ++ mu1).push 4) ∧
    s.ivPre = (Hs.hash .h3 ((wPrefix ++ mu1 ++ rho).push 3)).extract 16 32 ∧
    s.tree = (BAVC.commit s.seed s.iv).1 ∧ s.leaves = (BAVC.commit s.seed s.iv).2 ∧
    s.u = proverU p s.iv key 0 ∧
    s.fields.corrections = (List.range (BAVC.tau - 1)).foldl
      (fun acc j => acc ++ proverCorr p s.iv key (j + 1)) ByteArray.empty ∧
    s.fields.ivPre = s.ivPre ∧
    s.fields.qsProof = .empty ∧
    s.vRows = (crtReconstructWith (gateWords ((Prover.gateInputsOff p T s.iv
      (Prover.senderColumns p s.iv key) W128.zero).map (Hs.hash .h5))) p (fun _ => false)
      ByteArray.empty T (Prover.senderColumns p s.iv key)).rows ∧
    s.vRows.size = p.correctionRows ∧ s.vMask.size = p.nMask ∧ s.uMask.size = p.nMask ∧
    s.chal1 = chal1 Hs (step1Proof p s) mu1 (BAVC.check (Hs.hash .h1) s.leaves.coms) binder1 ∧
    s.fields.voleCheck = Prover.gfsToBytes (voleHashReceiver p s.chal1
      ((Array.range p.correctionRows).map fun r =>
        if wbit s.u r then (⟨1, 0⟩ : W128) else W128.zero)
      s.uMask 0 (Prover.zeros 64)) ∧
    s.hV = voleHashReceiver p s.chal1 s.vRows s.vMask 0 (Prover.zeros 64) := by
  intro s key
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl, rfl, rfl, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · show ((Array.range BAVC.tau).map (fun i => Prover.smallVoleUWords p s.iv i (key i)))[0]! = _
    rw [getElem!_range_map _ _ (show 0 < BAVC.tau by decide)]
    rfl
  · show (List.range (BAVC.tau - 1)).foldl (fun acc i => acc ++ Prover.correctionOf p
        ((Array.range BAVC.tau).map (fun i => Prover.smallVoleUWords p s.iv i (key i)))[0]!
        ((Array.range BAVC.tau).map (fun i => Prover.smallVoleUWords p s.iv i (key i)))[i + 1]!)
        ByteArray.empty = _
    refine List.foldl_ext _ _ _ fun acc j hj => ?_
    have hj := List.mem_range.1 hj
    simp only [proverCorr, proverU, getElem!_range_map _ _ (show 0 < BAVC.tau by decide),
      getElem!_range_map _ _ (show j + 1 < BAVC.tau by simp [BAVC.tau] at hj ⊢; omega)]
  · show ((Array.range p.correctionRows).map _).size = _
    simp
  · show ((Array.range p.nMask).map _).size = _
    simp
  · show ((Array.range p.nMask).map _).size = _
    simp

end VoleGen

/-! ## Completeness of the verifier on the prover's output -/

lemma size_foldl_append (L : List ByteArray) :
    (L.foldl (· ++ ·) ByteArray.empty).size = (L.map (·.size)).sum := by
  induction L with
  | nil => rfl
  | cons b L ih =>
    rw [List.foldl_cons, foldl_append_eq, ByteArray.size_append, ih]
    simp

lemma fit_empty (n : ℕ) : Prover.fit ByteArray.empty n = Prover.zeros n := by
  apply ByteArray.ext
  simp [Prover.fit, Prover.zeros]

lemma qsProve_aT_size {pf0 : Proof} {c2 : ByteArray} {values : (ℕ → GF128) → List GF128}
    {vRows vMask uMask : Array W128} {w : ByteArray} {check : GF128} {aT : Array GF128}
    (h : Prover.qsProve pf0 c2 values vRows vMask uMask w = .ok (check, aT)) :
    aT.size = pf0.params.qsDegree - 1 := by
  unfold Prover.qsProve at h
  dsimp only at h
  split_ifs at h
  all_goals first | (cases h; done) | skip
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  rw [← h.2]
  simp

/-- **BAVC completeness** (`one_tree_bavc::open`, then `verify`): an opening of the prover's tree
at `Δ` reconstructs the prover's leaf keys off the hidden leaves, and its commitments. Not proved
here (an imperative walk over the 4607 tree nodes); `lake exe prover_vectors` checks it on every
proof it produces (`ProverKats.checkCorrelation`). -/
def BAVCComplete : Prop :=
  ∀ seed iv delta o : ByteArray,
    BAVC.openAt (BAVC.commit seed iv).1 (BAVC.commit seed iv).2.coms delta = some o →
    ∃ leaves, BAVC.reconstruct iv (Prover.fit o BAVC.openSize) delta = some leaves ∧
      leaves.coms = (BAVC.commit seed iv).2.coms ∧
      ∀ i < BAVC.tau, ∀ j < 2 ^ BAVC.kOf i, j ≠ BAVC.deltaIndex delta i →
        leafKey leaves i j = leafKey (BAVC.commit seed iv).2 i j

/-- **CRT VOLE completeness for the prover's commitment** (`crt_vole_commit` against
`crt_vole_reconstruct`): at every `Δ`, the verifier's masks `q_mask[m]` are
`ṽ_mask[m] + u_mask[m]·Δ'`. This is the content of faest-arch-opt's CRT construction (the
garbled gate labels, `c_mult`, and the bilinear identity of `F`, `G`, `W_tree`, `W_gate` that
`CrtGen.identityOk` checks at run time); not proved here, checked on every proof by
`lake exe prover_vectors`. The rows are proved (`prover_row`). -/
def CrtComplete (h5 : ByteArray → ByteArray) (T : CrtTables) (s : Prover.Pending) : Prop :=
  ∀ dbit : ℕ → Bool, ∀ m < s.params.nMask,
    (crtReconstructAt h5 s.params dbit
      (Prover.fit s.fields.cmult (s.params.nMask * s.params.nMultBytes)) T s.iv
      (convertToVoleAt s.params dbit (proverCorr s.params s.iv (leafKey s.leaves)) s.iv
        (leafKey s.leaves))).qMask[m]!.toGF =
      s.vMask[m]!.toGF + s.uMask[m]!.toGF * (W128.rowMul dbit 120 T.wCrt).toGF

/-- **Completeness of the executable verifier on the executable prover's output.** If
`Prover.proveCommit` (after `Prover.voleGen` with the statement's `mu₁` and `chal1` binder)
returns a proof, the verifier accepts it, for any hash functions with the domains' output lengths
(`HashesWF`) and any statement whose evaluator is a system of degree `≤ d`, `1 ≤ d`
(`Bridge/Relations.lean`: all five relations). Assumed: BAVC completeness (`BAVCComplete`), the
CRT VOLE's mask correlation for this commitment (`CrtComplete`), and `Δ' ≠ 0` for the ground `Δ`
(probability `2⁻¹²⁰`; the C++ does not test it either). Everything else is proved: the VOLE
correlation of the rows (`prover_row`), the VOLE check (`voleHash_complete`, so the verifier
recomputes `chal1` and `chal2`), QuickSilver (`qsProve_complete`: the check value is the
prover's for every `Δ'`), and grinding (`chal3 = Δ`). -/
theorem verify_proveCommit (Hs : Hashes) (hHs : HashesWF Hs) (hbavc : BAVCComplete) (T : CrtTables)
    (st : Statement) (mu1 wPrefix rho binder1 wSuffix proof : ByteArray)
    (hmu : st.mu1 Hs = mu1) (hb1 : st.binder1 = binder1)
    (h : Prover.proveCommit Hs st wSuffix
      (Prover.voleGen Hs T st.params mu1 wPrefix rho binder1) = .ok proof)
    (hcrt : CrtComplete (Hs.hash .h5) T (Prover.voleGen Hs T st.params mu1 wPrefix rho binder1))
    (hΔ : (W128.rowMul (BAVC.deltaBit ({ params := st.params, bytes := proof } : Proof).delta) 120
      T.wCrt).toGF ≠ 0)
    (cs : ByteArray → ByteArray → System GF128)
    (hvals : ∀ c1 lb x, st.values c1 lb x = (cs c1 lb).values x)
    (hdeg : ∀ c1 lb, ∀ e ∈ cs c1 lb, e.degree ≤ st.params.qsDegree)
    (hd : 1 ≤ st.params.qsDegree) (hd' : st.params.qsDegree + 1 < 2 ^ 64) :
    (verify Hs T st proof).accept = true := by
  set p := st.params with hp
  have spec := voleGen_spec Hs T p mu1 wPrefix rho binder1
  have hinv := proveCommit_inv h
  generalize Prover.voleGen Hs T p mu1 wPrefix rho binder1 = s at spec hinv hcrt
  obtain ⟨hsp, hsw, hsiv, hsivp, hstree, hsleaves, hsu, hscorr, hsfiv, hsqs, hsvrows, hsvs, hsvm,
    hsum, hsc1, hsvc, hshv⟩ := spec
  dsimp only at hinv
  unfold CrtComplete at hcrt
  simp only [hsp] at hinv hcrt
  obtain ⟨hw, check, aT, ctr, delta, opening, hqsp, hfind, hproof⟩ := hinv
  obtain ⟨k, hk⟩ := findFirst_some _ _ _ hfind
  obtain ⟨hck, hdelta, h15, hopen⟩ := grindStep_some hk
  subst hck
  set key := leafKey s.leaves with hkey
  set w := s.wPrefix ++ wSuffix with hwdef
  set correction : ByteArray :=
    ⟨(Array.range p.witnessBytes).map fun k => (bytesOfWords s.u).get! k ^^^ w.get! k⟩ with hcorrdef
  set f1 : Prover.Fields :=
    { corrections := s.fields.corrections, cmult := s.fields.cmult,
      voleCheck := s.fields.voleCheck, correction := correction, qsProof := s.fields.qsProof,
      opening := s.fields.opening, delta := s.fields.delta, ivPre := s.fields.ivPre,
      ctr := s.fields.ctr } with hf1
  set pf1 : Proof := { params := p, bytes := Prover.assemble p f1 } with hpf1
  set c2 := chal2 Hs pf1 s.chal1 s.hV (st.muDelayed Hs s.chal1) st.binder2 with hc2
  set ff : Prover.Fields :=
    { corrections := f1.corrections, cmult := f1.cmult, voleCheck := f1.voleCheck,
      correction := f1.correction, qsProof := Prover.gfsToBytes aT, opening := opening,
      delta := delta, ivPre := f1.ivPre, ctr := AES.pushLE32 ByteArray.empty ctr.toUInt32 } with hff
  subst hproof
  set f0 : Prover.Fields := { s.fields with voleCheck := .empty, correction := .empty } with hf0
  obtain ⟨hC, hM, hV, hD, hQ, hO, hDl, hI, hCt, hSz⟩ := fields_assemble p ff
  obtain ⟨hC1, hM1, hV1, hD1, hQ1, -, -, -, -, -⟩ := fields_assemble p f1
  obtain ⟨hC0, hM0, -, -, -, -, -, hI0, -, -⟩ := fields_assemble p f0
  -- Sizes.
  have hd16 : delta.size = 16 := by rw [hdelta]; exact hHs _ _
  have hivs : s.ivPre.size = 16 := by rw [hsivp, ByteArray.size_extract, hHs]; rfl
  have hu : s.u.size = p.colBytes / 8 := by
    rw [hsu, proverU]
    exact (smallVoleUWords_spec p s.iv 0 (key 0) (r := 0) (by
      simp only [Params.colBytes, Params.voleColBlocks, Params.voleRows, Params.nMask]; omega)).1
  have hcsz : ∀ i, (proverCorr p s.iv key i).size = p.correctionBytes := fun i =>
    correctionOf_size p _ _ (by rw [← hsu]; exact hu)
  have hCsz : s.fields.corrections.size = 16 * p.correctionBytes := by
    rw [hscorr, show (List.range (BAVC.tau - 1)).foldl
        (fun acc j => acc ++ proverCorr p s.iv key (j + 1)) ByteArray.empty =
      ((List.range (BAVC.tau - 1)).map fun j => proverCorr p s.iv key (j + 1)).foldl (· ++ ·)
        ByteArray.empty by simp [List.foldl_map], size_foldl_append, List.map_map]
    simp only [Function.comp_def, hcsz, List.map_const', List.length_range, List.sum_replicate,
      smul_eq_mul]
    rfl
  have hvcs : s.fields.voleCheck.size = 64 := by rw [hsvc, gfsToBytes_size, voleHashReceiver_size]
  have hcorrs : correction.size = p.witnessBytes := by simp [correction, ByteArray.size]
  have haTs := qsProve_aT_size hqsp
  -- The fields of the final proof.
  have pfDelta : ({ params := p, bytes := Prover.assemble p ff } : Proof).delta = delta := by
    rw [hDl]; exact fit_of_size hd16
  have pfIv : ({ params := p, bytes := Prover.assemble p ff } : Proof).ivPre = s.ivPre := by
    rw [hI]; show Prover.fit s.fields.ivPre 16 = _; rw [hsfiv]; exact fit_of_size hivs
  have pfOpen : ({ params := p, bytes := Prover.assemble p ff } : Proof).opening =
      Prover.fit opening BAVC.openSize := hO
  have pfCorr : ∀ i, 1 ≤ i → i < BAVC.tau →
      ({ params := p, bytes := Prover.assemble p ff } : Proof).correctionOf i =
        proverCorr p s.iv key i := by
    intro i hi1 hi
    rw [Proof.correctionOf, hC, show ff.corrections = s.fields.corrections from rfl,
      fit_of_size hCsz, hscorr]
    exact correctionOf_concat p (proverCorr p s.iv key) hcsz hi1 hi
  have pfCm : ({ params := p, bytes := Prover.assemble p ff } : Proof).cmult =
      Prover.fit s.fields.cmult (p.nMask * p.nMultBytes) := hM
  have pfVc :
      ({ params := p, bytes := Prover.assemble p ff } : Proof).voleCheck = s.fields.voleCheck := by
    rw [hV]; exact fit_of_size hvcs
  have pfD : ({ params := p, bytes := Prover.assemble p ff } : Proof).correction = correction := by
    rw [hD]; exact fit_of_size hcorrs
  have pfQs :
      ({ params := p, bytes := Prover.assemble p ff } : Proof).qsProof = Prover.gfsToBytes aT := by
    rw [hQ]; exact fit_of_size (by rw [gfsToBytes_size, haTs]; ring)
  have pfCt : ({ params := p, bytes := Prover.assemble p ff } : Proof).ctr =
      AES.pushLE32 ByteArray.empty ctr.toUInt32 := by
    rw [hCt]; exact fit_of_size (pushLE32_size _)
  set pf : Proof := { params := p, bytes := Prover.assemble p ff } with hpfdef
  -- The verifier's run.
  have hiv : ivOf Hs pf (st.mu1 Hs) = s.iv := by rw [hmu, ivOf, pfIv, hsiv]
  obtain ⟨leaves, hrec, hcoms, hkeys⟩ :=
    hbavc s.seed s.iv delta opening (by rw [← hstree, ← hsleaves]; exact hopen)
  rw [← hsleaves] at hcoms hkeys
  apply (accept_iff Hs T st _).2
  refine ⟨?_, leaves, ?_, ?_⟩
  · show (pf.bytes.size == p.proofBytes && pf.delta.get! 15 == 0) = true
    rw [pfDelta, h15, hSz]
    simp
  · show BAVC.reconstruct (ivOf Hs pf (st.mu1 Hs)) pf.opening pf.delta = some leaves
    rw [hiv, pfOpen, pfDelta]; exact hrec
  intro c1 crt deltaL hVv c2v csv
  have hc1 : c1 = s.chal1 := by
    show chal1 Hs pf (st.mu1 Hs) (BAVC.check (Hs.hash .h1) leaves.coms) st.binder1 = s.chal1
    rw [hsc1, hmu, hcoms, hb1]
    simp only [chal1, chal1Input, step1Proof]
    rw [hC, hM, hI, hC0, hM0, hI0]
  have hcols : convertToVole pf (ivOf Hs pf (st.mu1 Hs)) leaves =
      convertToVoleAt p (BAVC.deltaBit delta) (proverCorr p s.iv key) s.iv key := by
    rw [hiv, convertToVole, pfDelta,
      convertToVoleAt_congr_key p _ _ s.iv (key' := key) fun i hi j hj hjd => hkeys i hi j hj hjd]
    exact convertToVoleAt_congr_corr p _ s.iv key pfCorr
  have hcrt' : crt = crtReconstructAt (Hs.hash .h5) p (BAVC.deltaBit delta)
      (Prover.fit s.fields.cmult (p.nMask * p.nMultBytes)) T s.iv
      (convertToVoleAt p (BAVC.deltaBit delta) (proverCorr p s.iv key) s.iv key) := by
    show crtReconstruct Hs pf T (ivOf Hs pf (st.mu1 Hs))
      (convertToVole pf (ivOf Hs pf (st.mu1 Hs)) leaves) = _
    rw [hcols, crtReconstruct, pfDelta, pfCm, hiv]
  have hdl : deltaL = (W128.rowMul (BAVC.deltaBit delta) 120 T.wCrt).toGF := by
    show crt.deltaLifted.toGF = _
    rw [hcrt']; rfl
  have hrows : ∀ r < p.correctionRows,
      crt.rows[r]!.toGF = s.vRows[r]!.toGF + (if wbit s.u r then 1 else 0) * deltaL := by
    intro r hr
    rw [hcrt', hdl, prover_row _ (gateWords ((Prover.gateInputsOff p T s.iv
      (Prover.senderColumns p s.iv key) W128.zero).map (Hs.hash .h5))) _ _ _ ByteArray.empty _ _ _
      hr,
      hsvrows, hsu]
  have hmask : ∀ m < p.nMask,
      crt.qMask[m]!.toGF = s.vMask[m]!.toGF + s.uMask[m]!.toGF * deltaL := by
    intro m hm
    rw [hcrt', hdl]
    exact hcrt _ m hm
  have hrs : crt.rows.size = p.correctionRows := by
    rw [hcrt']; simp only [crtReconstructAt, crtReconstructWith, Array.size_map, Array.size_range]
  have hms : crt.qMask.size = p.nMask := by
    rw [hcrt']; simp only [crtReconstructAt, crtReconstructWith, Array.size_map, Array.size_range]
  have hhV : hVv = s.hV := by
    show voleHashReceiver p c1 crt.rows crt.qMask deltaL pf.voleCheck = s.hV
    rw [hc1, pfVc, hsvc, hshv]
    exact voleHash_complete p s.chal1 s.vRows s.vMask s.uMask crt.rows crt.qMask s.u deltaL _ _
      hrs hsvs hms hsvm hsum hrows hmask
  have hc2v : c2v = c2 := by
    show chal2 Hs pf c1 hVv (st.muDelayed Hs c1) st.binder2 = c2
    rw [hc1, hhV, hc2]
    simp only [chal2, chal2Input]
    rw [hV, hD, hV1, hD1]
  have hΔ' : deltaL ≠ 0 := by rw [hdl, ← pfDelta]; exact hΔ
  refine ⟨hΔ', ?_⟩
  -- QuickSilver: the check value is the prover's.
  have hkeys' : correctedKeys pf crt.rows deltaL = Prover.qsKeys p s.vRows w deltaL :=
    correctedKeys_prover pf crt.rows s.vRows s.u w deltaL
      (by
        show p.witnessBits ≤ 64 * s.u.size
        have := correctionRows_lt p; simp only [Params.correctionRows] at this; rw [hu]; omega)
      (fun r hr => hrows r (by
        have hr' : r < p.witnessBits := hr
        simp only [Params.correctionRows]; omega)) pfD
  have hmasks : crt.qMask = Prover.qsMasks p s.vMask s.uMask deltaL := by
    apply Array.ext
    · simp [Prover.qsMasks, hms]
    intro m h1 h2
    have hm : m < p.nMask := by rwa [hms] at h1
    rw [← getElem!_pos crt.qMask m h1]
    simp only [Prover.qsMasks, Array.getElem_map, Array.getElem_range, ← hmask m hm]
    rfl
  have h0 : ∀ i, gfOfBytes pf1.qsProof (16 * i) = 0 := by
    intro i
    rw [hQ1, show f1.qsProof = s.fields.qsProof from rfl, hsqs, fit_empty, gfOfBytes_zeros]
  have hqs := qsProve_complete pf1 c2 _ s.vRows s.vMask s.uMask w hqsp
    (cs s.chal1 (st.combBytes Hs c2))
    (hvals _ _) (hdeg _ _) hd hd' h0 pf rfl pfQs hΔ'
  have hcheck : qsCheck pf c2v (constraintKeys st.params (correctedKeys pf crt.rows deltaL) deltaL
      (st.values c1 (st.combBytes Hs c2v))) crt.qMask deltaL = check := by
    rw [hkeys', hmasks, hc1, hc2v]
    exact hqs
  show chal3 Hs pf c2v (qsCheck pf c2v (constraintKeys st.params (correctedKeys pf crt.rows deltaL)
    deltaL (st.values c1 (st.combBytes Hs c2v))) crt.qMask deltaL) = pf.delta
  rw [hcheck, pfDelta, hdelta, chal3, chal3Input, pfQs, pfCt, hc2v, ← pushLE32_eq]

/-- **Completeness for `Prover.prove`** (no delayed instance binding: step 1 with the witness
prefix, the statement's `mu₁` and binder). -/
theorem verify_prove (Hs : Hashes) (hHs : HashesWF Hs) (hbavc : BAVCComplete) (T : CrtTables)
    (st : Statement) (w rho : ByteArray) (prefixBytes : ℕ) (proof : ByteArray)
    (h : Prover.prove Hs T st w rho prefixBytes = .ok proof)
    (hcrt : CrtComplete (Hs.hash .h5) T
      (Prover.voleGen Hs T st.params (st.mu1 Hs) (w.extract 0 prefixBytes) rho st.binder1))
    (hΔ : (W128.rowMul (BAVC.deltaBit ({ params := st.params, bytes := proof } : Proof).delta) 120
      T.wCrt).toGF ≠ 0)
    (cs : ByteArray → ByteArray → System GF128)
    (hvals : ∀ c1 lb x, st.values c1 lb x = (cs c1 lb).values x)
    (hdeg : ∀ c1 lb, ∀ e ∈ cs c1 lb, e.degree ≤ st.params.qsDegree)
    (hd : 1 ≤ st.params.qsDegree) (hd' : st.params.qsDegree + 1 < 2 ^ 64) :
    (verify Hs T st proof).accept = true :=
  verify_proveCommit Hs hHs hbavc T st _ _ rho _ _ proof rfl rfl h hcrt hΔ cs hvals hdeg hd hd'

/-! ### Per relation

The four relations without delayed instance binding, with the systems and degree bounds of
`Bridge/Relations.lean` (`*_values`, `EndToEnd/Degree.lean`). Their C++ prover passes the whole
witness to step 1 (`WITNESS_PREFIX_BYTES = WITNESS_BYTES`), as `Prover.prove`'s default. -/

/-- The hypotheses of `verify_prove` that are not about the relation. -/
def ProveOk (Hs : Hashes) (T : CrtTables) (st : Statement) (w rho proof : ByteArray) : Prop :=
  Prover.prove Hs T st w rho = .ok proof ∧
    CrtComplete (Hs.hash .h5) T (Prover.voleGen Hs T st.params (st.mu1 Hs)
      (w.extract 0 st.params.witnessBytes) rho st.binder1) ∧
    (W128.rowMul (BAVC.deltaBit ({ params := st.params, bytes := proof } : Proof).delta) 120
      T.wCrt).toGF ≠ 0

theorem moussakaIssue_complete (Hs : Hashes) (hHs : HashesWF Hs) (hbavc : BAVCComplete)
    (T : CrtTables) (t ctxIss : ByteArray) (labelRows : Bool) (w rho proof : ByteArray)
    (h : ProveOk Hs T (moussakaIssue t ctxIss labelRows) w rho proof) :
    (verify Hs T (moussakaIssue t ctxIss labelRows) proof).accept = true :=
  verify_prove Hs hHs hbavc T _ w rho _ proof h.1 h.2.1 h.2.2 _
    (moussakaIssue_values t ctxIss labelRows) (fun _ _ => Degree.moussaka_issue_deg _ _)
    (by show 1 ≤ 9; norm_num) (by show 9 + 1 < 2 ^ 64; norm_num)

theorem moussakaRedeem_complete (Hs : Hashes) (hHs : HashesWF Hs) (hbavc : BAVCComplete)
    (T : CrtTables) (anchors : List UovPk) (nf ctxIss ctxRed challengeDigest : ByteArray)
    (labelRows : Bool) (w rho proof : ByteArray)
    (h : ProveOk Hs T (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows) w rho
      proof) :
    (verify Hs T (moussakaRedeem anchors nf ctxIss ctxRed challengeDigest labelRows)
      proof).accept = true :=
  verify_prove Hs hHs hbavc T _ w rho _ proof h.1 h.2.1 h.2.2 _
    (moussakaRedeem_values anchors nf ctxIss ctxRed challengeDigest labelRows)
    (fun _ _ => Degree.moussaka_redeem_deg _ _ _ _ _ _ _)
    (by show 1 ≤ 9; norm_num) (by show 9 + 1 < 2 ^ 64; norm_num)

theorem ratatouilleIssue_complete (Hs : Hashes) (hHs : HashesWF Hs) (hbavc : BAVCComplete)
    (T : CrtTables) (c : ByteArray) (tInit : ℕ) (ctxIss : ByteArray) (labelRows : Bool)
    (w rho proof : ByteArray)
    (h : ProveOk Hs T (ratatouilleIssue c tInit ctxIss labelRows) w rho proof) :
    (verify Hs T (ratatouilleIssue c tInit ctxIss labelRows) proof).accept = true :=
  verify_prove Hs hHs hbavc T _ w rho _ proof h.1 h.2.1 h.2.2 _
    (ratatouilleIssue_values c tInit ctxIss labelRows)
    (fun _ _ => Degree.ratatouille_issue_deg _ _ _)
    (by show 1 ≤ 9; norm_num) (by show 9 + 1 < 2 ^ 64; norm_num)

theorem ratatouilleSpend_complete (Hs : Hashes) (hHs : HashesWF Hs) (hbavc : BAVCComplete)
    (T : CrtTables) (pk : UovPk) (nf : ByteArray) (d : ℕ) (cNext ctxIss : ByteArray)
    (labelRows : Bool) (w rho proof : ByteArray)
    (h : ProveOk Hs T (ratatouilleSpend pk nf d cNext ctxIss labelRows) w rho proof) :
    (verify Hs T (ratatouilleSpend pk nf d cNext ctxIss labelRows) proof).accept = true :=
  verify_prove Hs hHs hbavc T _ w rho _ proof h.1 h.2.1 h.2.2 _
    (ratatouilleSpend_values pk nf d cNext ctxIss labelRows)
    (fun _ _ => Degree.ratatouille_spend_deg _ _ _ _ _ _ _ _)
    (by show 1 ≤ 9; norm_num) (by show 9 + 1 < 2 ^ 64; norm_num)

/-- The size of the proof written by step 1. -/
lemma Pending_proof_size (s : Prover.Pending) : s.proof.size = s.params.proofBytes :=
  (fields_assemble s.params s.fields).2.2.2.2.2.2.2.2.2

/-- The PomFRIT prover's step 1 (`issue_request_with_seed`): `voleGen` with the witness prefix `r`,
`mu₁ = H₂⁴(DST ‖ 12)` and the binder `refresher_com`. -/
def pomfritPending (Hs : Hashes) (T : CrtTables) (labelRows : Bool) (r rho com : ByteArray) :
    Prover.Pending :=
  Prover.voleGen Hs T (pomfritParams labelRows) (mu Hs none (toBA (Spec.makeDst "pomf" 0 'p' '0')))
    r rho com

/-- **PomFRIT redemption: completeness** of the two-step prover (`finalize_issue`'s
`proveCommit` with the Signer's preimage `s`), for the statement it proves, built from step 1's
signature `proof₁ ‖ refresher_com ‖ refresher` (whose `ũ` and `d[0..45)` give the target `h`). -/
theorem pomfritRedeem_complete (Hs : Hashes) (hHs : HashesWF Hs) (hbavc : BAVCComplete)
    (T : CrtTables) (pk : UovPk) (msg r rho com refresher wSuffix proof : ByteArray)
    (labelRows : Bool) (hcom : com.size = 32)
    (h : Prover.proveCommit Hs (pomfritRedeem pk
      ((pomfritPending Hs T labelRows r rho com).proof ++ com ++ refresher) msg labelRows) wSuffix
      (pomfritPending Hs T labelRows r rho com) = .ok proof)
    (hcrt : CrtComplete (Hs.hash .h5) T (pomfritPending Hs T labelRows r rho com))
    (hΔ : (W128.rowMul (BAVC.deltaBit
      ({ params := pomfritParams labelRows, bytes := proof } : Proof).delta) 120 T.wCrt).toGF ≠ 0) :
    (verify Hs T (pomfritRedeem pk ((pomfritPending Hs T labelRows r rho com).proof ++ com ++
      refresher) msg labelRows) proof).accept = true := by
  have hsz : (pomfritPending Hs T labelRows r rho com).proof.size =
      (pomfritParams labelRows).proofBytes := Pending_proof_size _
  refine verify_proveCommit Hs hHs hbavc T _ _ r rho com wSuffix proof rfl ?_ h hcrt hΔ _
    (pomfritRedeem_values pk _ msg labelRows)
    (fun _ _ => PomFRIT.degree_pomfritRedeemSystem _ _ _ _ _ _ _)
    (by show 1 ≤ 2; norm_num) (by show 2 + 1 < 2 ^ 64; norm_num)
  show ((pomfritPending Hs T labelRows r rho com).proof ++ com ++ refresher).extract
    (pomfritParams labelRows).proofBytes ((pomfritParams labelRows).proofBytes + 32) = com
  have e := ByteArray.extract_append_size_add (a := (pomfritPending Hs T labelRows r rho com).proof)
    (b := com ++ refresher) (i := 0) (j := com.size)
  rw [Nat.add_zero] at e
  rw [← hsz, ByteArray.append_assoc, ← hcom, e]
  exact extract_append_left' com refresher

end

end VoleMole.Verifier.Bridge
