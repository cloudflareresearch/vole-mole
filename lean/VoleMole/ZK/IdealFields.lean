import VoleMole.ZK.ByteLemmas
import VoleMole.ZK.CrtMask

/-!
# The ideal-tape prover's fields as functions of its pads

`Sim.idealCore` computes the corrections, `d`, the bits of `u` on the corrected rows and `u_mask`
from the small VOLEs' inputs `u^{(i)}` as words (`usOf`), as the real prover does. Here they are
read off the pads directly (`idealCore_eq`):

* `corrB t`: the corrections `c_i = u^{(0)} ⊕ u^{(i)}` on the corrected rows, byte by byte;
* `dB t`: `d = u^{(0)} ⊕ w` on the witness rows;
* `ubitF t`: the bits of `u = u^{(0)}` on the corrected rows (witness rows `u0w`, label rows `θ`);
* `uMaskArr t`: `u_mask[m] = crtW` of byte `m` of each tree's mask-row pad and of `u_hi`
  (`ZK/CrtMask.lean`).

So the corrections, `d` and the bits of `u` depend on the row pads only, `u_mask` on the mask
pads only, and only `c_mult` (`cmultIdeal`) reads the sibling hashes. `ZK/IdealSim.lean` turns
this into the zero-knowledge statement.
-/

namespace VoleMole.ZK.Sim

-- The statements hold for any CTR PRG (`HasPrg`, `Verifier/Prg.lean`), AES included.
variable [VoleMole.Verifier.HasPrg]
set_option linter.unusedSectionVars false

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith

variable {p : Params}

/-! ## Sizes -/

lemma wb_le_cb (p : Params) : p.witnessBytes ≤ p.correctionBytes := by
  simp only [Params.correctionBytes, Params.correctionRows, Params.witnessBits]; split <;> omega

lemma cb_add_nMask_le (p : Params) : p.correctionBytes + p.nMask ≤ p.colBytes := by
  simp only [Params.colBytes, Params.voleColBlocks, Params.voleRows, Params.correctionBytes,
    Params.correctionRows, Params.witnessBits]
  split <;> omega

lemma colBytes_mod8 (p : Params) : p.colBytes % 8 = 0 := by
  simp only [Params.colBytes]; omega

lemma tau_sub_one : BAVC.tau - 1 = 16 := rfl

lemma labelBytes_add (p : Params) : p.witnessBytes + labelBytes p = p.correctionBytes := by
  have := wb_le_cb p; simp only [labelBytes]; omega

/-- `u^{(0)}` on the corrected rows: the witness-row pad and the label-row pad. -/
def U0 (t : Pads p) : ByteArray := ba t.1 ++ ba t.2.1

lemma U0_size (t : Pads p) : (U0 t).size = p.correctionBytes := by
  simp [U0, ByteArray.size_append, labelBytes_add]

lemma usBytes_size (t : Pads p) {i : ℕ} (hi : i < BAVC.tau) : (usBytes p t i).size = p.colBytes := by
  have h1 := cb_add_nMask_le p
  unfold usBytes
  by_cases h0 : i = 0
  · subst h0
    simp only [↓reduceIte, ByteArray.size_append, size_ba, hi, dite_true]
    simp only [restBytes]; have := labelBytes_add p; omega
  · have hi' : i - 1 < BAVC.tau - 1 := by omega
    simp only [h0, ↓reduceIte, hi', dite_true, ByteArray.size_append, size_ba, hi, restBytes]
    omega

/-- The bytes of `u^{(i)}` on the corrected rows. -/
lemma usBytes_get_corr (t : Pads p) {i : ℕ} (hi : i < BAVC.tau) {k : ℕ}
    (hk : k < p.correctionBytes) :
    (usBytes p t i).get! k =
      if h : i = 0 then (U0 t).get! k else (ba (t.2.2.1 ⟨i - 1, by omega⟩)).get! k := by
  unfold usBytes
  rw [get!_append]
  by_cases h0 : i = 0
  · subst h0
    have : k < (ba t.1 ++ ba t.2.1).size := by rw [← U0, U0_size]; exact hk
    simp only [↓reduceIte, this, dite_true]
    rfl
  · have hi' : i - 1 < BAVC.tau - 1 := by omega
    simp [h0, hi', hk]

/-- Byte `cb + m` of `u^{(i)}` is the tape's mask-row pad. -/
lemma usBytes_get_mask (t : Pads p) {i : ℕ} (hi : i < BAVC.tau) {m : ℕ} (hm : m < p.nMask) :
    (usBytes p t i).get! (p.correctionBytes + m) = t.2.2.2.1 ⟨i, hi⟩ ⟨m, hm⟩ := by
  unfold usBytes
  rw [get!_append]
  have hsz : (if i = 0 then ba t.1 ++ ba t.2.1
      else if h' : i - 1 < BAVC.tau - 1 then ba (t.2.2.1 ⟨i - 1, h'⟩) else ByteArray.empty).size =
      p.correctionBytes := by
    by_cases h0 : i = 0
    · simp only [h0, ↓reduceIte]; rw [← U0, U0_size]
    · simp only [h0, ↓reduceIte, show i - 1 < BAVC.tau - 1 by omega, dite_true, size_ba]
  rw [hsz]
  simp only [show ¬ p.correctionBytes + m < p.correctionBytes by omega, ↓reduceIte, hi, dite_true,
    Nat.add_sub_cancel_left, get!_append, size_ba, hm, get!_ba _ hm]

/-! ## The words -/

lemma usOf_size (t : Pads p) : (usOf p t).size = BAVC.tau := by simp [usOf]

lemma usOf_get (t : Pads p) {i : ℕ} (hi : i < BAVC.tau) :
    (usOf p t)[i]! = wordsOf (usBytes p t i) := by
  rw [usOf, getElem!_range_map _ _ hi]

lemma usOf_get_size (t : Pads p) {i : ℕ} (hi : i < BAVC.tau) :
    ((usOf p t)[i]!).size = p.colBytes / 8 := by
  rw [usOf_get t hi]; simp [wordsOf, usBytes_size t hi]

lemma bytesOfWords_usOf (t : Pads p) {i : ℕ} (hi : i < BAVC.tau) :
    bytesOfWords (usOf p t)[i]! = usBytes p t i := by
  rw [usOf_get t hi, bytesOfWords_wordsOf (by rw [usBytes_size t hi]; exact colBytes_mod8 p)]

/-- Bit `r` of a small VOLE's input, from its bytes. -/
lemma wbit_usOf (t : Pads p) {i : ℕ} (hi : i < BAVC.tau) {r : ℕ} (hr : r < 8 * p.colBytes) :
    wbit (usOf p t)[i]! r = ((usBytes p t i).get! (r / 8)).toNat.testBit (r % 8) := by
  rw [usOf_get t hi, wbit_wordsOf _ (by rw [usBytes_size t hi]; have := colBytes_mod8 p; omega)]

/-! ## The corrections, `d` and the bits of `u` -/

/-- The corrections from the pads: byte `k` of `c_{i+1}` is `u^{(0)}[k] ⊕ u^{(i+1)}[k]`. -/
def corrB (t : Pads p) : Bytes (16 * p.correctionBytes) := fun j =>
  (U0 t).get! (j % p.correctionBytes) ^^^
    (ba (t.2.2.1 ⟨j / p.correctionBytes, by
      have := j.isLt; rw [tau_sub_one]; exact Nat.div_lt_of_lt_mul (by linarith)⟩)).get!
      (j % p.correctionBytes)

/-- `d` from the pads. -/
def dB (w : ByteArray) (t : Pads p) : Bytes p.witnessBytes := fun k => t.1 k ^^^ w.get! k

/-- The bits of `u` on the corrected rows, from the pads. -/
def ubitF (t : Pads p) (r : ℕ) : Bool := ((U0 t).get! (r / 8)).toNat.testBit (r % 8)

/-- The masks from the pads (`ZK/CrtMask.lean`'s `crtW`). -/
def uMaskArr (T : CrtTables) (t : Pads p) : Array W128 :=
  (Array.range p.nMask).map fun m =>
    crtW T (fun i => (ba (t.2.2.2.1 i)).get! m) ((ba t.2.2.2.2.2.1).get! m)

lemma correctionOf_get (t : Pads p) {i : ℕ} (hi : i + 1 < BAVC.tau) {k : ℕ}
    (hk : k < p.correctionBytes) :
    (Prover.correctionOf p (usOf p t)[0]! (usOf p t)[i + 1]!).get! k =
      (U0 t).get! k ^^^ (ba (t.2.2.1 ⟨i, by omega⟩)).get! k := by
  have h8 := cb_add_nMask_le p
  rw [Prover.correctionOf, get!_extract0 _ hk (by
      rw [bytesOfWords_size, xorWords_size, usOf_get_size t (by decide)]
      have := colBytes_mod8 p; omega),
    bytesOfWords_xorWords_get _ _ (by rw [usOf_get_size t (by decide), usOf_get_size t hi])
      (by rw [usOf_get_size t (by decide)]; have := colBytes_mod8 p; omega),
    bytesOfWords_usOf t (by decide), bytesOfWords_usOf t hi,
    usBytes_get_corr t (by decide) hk, usBytes_get_corr t hi hk]
  simp

lemma correctionOf_size' (t : Pads p) (i : ℕ) :
    (Prover.correctionOf p (usOf p t)[0]! (usOf p t)[i + 1]!).size = p.correctionBytes :=
  correctionOf_size p _ _ (usOf_get_size t (by decide))

/-- **The corrections are `corrB`.** -/
theorem correctionsOf_eq (t : Pads p) : correctionsOf p (usOf p t) = ba (corrB t) := by
  have hm : ∀ i, i < BAVC.tau - 1 →
      (Prover.correctionOf p (usOf p t)[0]! (usOf p t)[i + 1]!).size = p.correctionBytes :=
    fun i _ => correctionOf_size' t i
  have hsz : (correctionsOf p (usOf p t)).size = 16 * p.correctionBytes := by
    rw [correctionsOf, size_foldl_append']
    simp only [ByteArray.size_empty, Nat.zero_add]
    rw [List.map_congr_left fun i hi => hm i (List.mem_range.1 hi)]
    simp only [List.map_const', List.length_range, tau_sub_one, List.sum_replicate, smul_eq_mul]
  apply byteArray_ext_get!
  · rw [hsz, size_ba]
  intro j hj
  rw [hsz] at hj
  have hcb : 0 < p.correctionBytes := by
    rcases Nat.eq_zero_or_pos p.correctionBytes with h | h
    · rw [h] at hj; simp at hj
    · exact h
  have hq : j / p.correctionBytes < 16 := Nat.div_lt_of_lt_mul (by linarith)
  -- Pad every block to the same size, then read the block.
  let f : ℕ → ByteArray := fun i =>
    if i < BAVC.tau - 1 then Prover.correctionOf p (usOf p t)[0]! (usOf p t)[i + 1]!
    else Prover.zeros p.correctionBytes
  have hf : ∀ i, (f i).size = p.correctionBytes := fun i => by
    simp only [f]; split_ifs with h
    · exact hm i h
    · exact zeros_size _
  have hfold : correctionsOf p (usOf p t) =
      (List.range (BAVC.tau - 1)).foldl (fun acc i => acc ++ f i) ByteArray.empty := by
    refine List.foldl_ext _ _ _ fun acc i hi => ?_
    simp only [f, List.mem_range.1 hi, ↓reduceIte]
  rw [hfold, get!_foldl_blocks f _ hf _ _ (by rw [tau_sub_one]; linarith)]
  simp only [f, show j / p.correctionBytes < BAVC.tau - 1 by rw [tau_sub_one]; exact hq, ↓reduceIte]
  have htau : BAVC.tau = 17 := rfl
  rw [correctionOf_get t (by rw [htau]; omega) (Nat.mod_lt _ hcb),
    get!_ba _ hj]
  rfl

/-- **The witness correction is `dB`.** -/
theorem correction_eq (w : ByteArray) (t : Pads p) :
    (⟨(Array.range p.witnessBytes).map fun k =>
      (bytesOfWords (usOf p t)[0]!).get! k ^^^ w.get! k⟩ : ByteArray) = ba (dB w t) := by
  apply byteArray_ext_get!
  · rw [size_ba]; show ((Array.range p.witnessBytes).map _).size = _; simp
  intro k hk
  have hk' : k < p.witnessBytes := by
    have : ((Array.range p.witnessBytes).map fun k =>
      (bytesOfWords (usOf p t)[0]!).get! k ^^^ w.get! k).size = p.witnessBytes := by simp
    exact this ▸ hk
  rw [get!_ba _ hk']
  rw [byteArray_get!_eq]
  simp only [Array.getElem?_map, Array.getElem?_range, hk', ↓reduceIte, Option.map_some,
    Option.getD_some]
  rw [bytesOfWords_usOf t (by decide), usBytes_get_corr t (by decide)
    (lt_of_lt_of_le hk' (wb_le_cb p))]
  simp only [dite_true, U0, get!_append, size_ba, hk', ↓reduceIte, get!_ba _ hk', dB]

/-- **The bits of `u` on the corrected rows are `ubitF`.** -/
theorem wbit_u_eq (t : Pads p) {r : ℕ} (hr : r < p.correctionRows) :
    wbit (usOf p t)[0]! r = ubitF t r := by
  have hcb := correctionBytes_mul p
  have h1 := cb_add_nMask_le p
  rw [wbit_usOf t (by decide) (by omega), usBytes_get_corr t (by decide) (by omega)]
  rfl

lemma rowMul_congr {x x' : ℕ → Bool} {n : ℕ} (M : Array W128) (h : ∀ c < n, x c = x' c) :
    W128.rowMul x n M = W128.rowMul x' n M := by
  simp only [W128.rowMul, Id.run, bind_pure]
  rw [forIn_range_foldl _ _ _ (fun i acc => if x i then acc.xor M[i]! else acc)
      fun i b => by split_ifs <;> rfl,
    forIn_range_foldl _ _ _ (fun i acc => if x' i then acc.xor M[i]! else acc)
      fun i b => by split_ifs <;> rfl]
  congr 1
  exact List.foldl_ext _ _ _ fun acc c hc => by rw [h c (List.mem_range.1 hc)]

/-- **The masks are `uMaskArr`.** -/
theorem uMask_eq (T : CrtTables) (t : Pads p) :
    uMaskOfHi p T (ba t.2.2.2.2.2.1) (usOf p t) = uMaskArr T t := by
  have hcb := correctionBytes_mul p
  have h1 := cb_add_nMask_le p
  refine Array.map_congr_left fun m hm => ?_
  have hm' := Array.mem_range.1 hm
  simp only [crtW]
  congr 1
  refine rowMul_congr _ fun c hc => ?_
  obtain ⟨hi, hle, hb⟩ := treeOf_spec hc
  have hb8 : c - BAVC.bitOffset (BAVC.treeOf c) < 8 := lt_of_lt_of_le hb (by
    rw [kOf_eq]; split_ifs <;> omega)
  rw [wbit_usOf t hi (by omega)]
  have e1 : (p.correctionRows + 8 * m + (c - BAVC.bitOffset (BAVC.treeOf c))) / 8 =
      p.correctionBytes + m := by omega
  have e2 : (p.correctionRows + 8 * m + (c - BAVC.bitOffset (BAVC.treeOf c))) % 8 =
      c - BAVC.bitOffset (BAVC.treeOf c) := by omega
  rw [e1, e2, usBytes_get_mask t hi hm', crtLow]
  simp only [hi, dite_true, get!_ba _ hm']

/-- **The ideal prover's run, from its pads**: the corrections, `d`, the bits of `u` and the masks
are read off the pads (`corrB`, `dB`, `ubitF`, `uMaskArr`). -/
theorem idealCore_eq (Hs : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray) (s : Shared)
    (ctr : ℕ) (delta : Bytes 16) (t : Pads st.params) :
    idealCore Hs T st w s ctr delta t =
      idealTail Hs T st w s ctr delta (ba (corrB t))
        (cmultIdeal Hs T st (pubOf Hs st s delta) delta
          (qcolsOf st (pubOf Hs st s delta) delta (ba (corrB t))) (usOf st.params t)[0]!
          (uMaskArr T t) t.2.2.2.2.2.2)
        (uMaskArr T t) ((Array.range st.params.correctionRows).map (ubitF t)) (ba (dB w t)) := by
  unfold idealCore
  simp only
  rw [correctionsOf_eq, uMask_eq, correction_eq,
    Array.map_congr_left fun r hr => wbit_u_eq t (Array.mem_range.1 hr)]

end VoleMole.ZK.Sim
