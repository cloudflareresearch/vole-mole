import VoleMole.Verifier.Bridge.Lift
import VoleMole.Verifier.VOLE

/-!
# Bridge: ConvertToVOLE and the lifted rows as functions of `Δ`

`Verifier/VOLE.lean` computes the verifier's key columns from the BAVC leaves at the proof's `Δ`
(`convertToVoleAt`, `treeColumns`) and lifts the rows with `W_CRT` (`crtReconstructAt`). Here both
are read as functions of the challenge, with the prover's commitments fixed: the corrections
`c_i`, and the leaf keys `K i j` that the commitment determines (L1). The result is the per-tree
affine form that `Claim4Hyp.tree_form` assumes.

## Columns (`treeColumns_bit`, `treeColumns_affine`)

For small VOLE `i` with hidden index `dI`, column `p_i + b` (`b < k_i`) of the verifier's key
matrix is, bit by bit (row `r`, in `F₂`),

  `q_{p_i+b}[r] = dI_b · c_i[r] + Σ_{j < 2^{k_i}, j ≠ dI} (j ⊕ dI)_b · R_j[r]`,

the executable fold written out. Since `(dI ⊕ dI)_b = 0` and `(j ⊕ dI)_b = j_b + dI_b`, this is

  `q_{p_i+b}[r] = V_{i,b}[r] + dI_b · u^{(i)}[r]`,   `V_{i,b} = Σ_j j_b R_j`, `u^{(i)} = c_i + Σ_j R_j`,

where `R_j = PRG(K i j, iv, 2³¹ + i)` and the sums run over all leaves: the hidden leaf's key is
never read, so `K i dI` may be anything. `u^{(i)}` (`smallVoleU`) is exactly the extractor's
corrected small-VOLE value: computable from the committed keys of tree `i` alone.

## Rows (`resp_row`)

The lifted row `r < ℓ'` is `Σ_{c < 120} q_c[r] · W_CRT[c]`. Regrouping the 120 columns by tree
(`sum_range_120`) and using `testBit_hiddenIndex` (`dI_b = Δ_{i,b}`):

  `row_r(Δ') = C_r + Σ_i u^{(i)}[r] · e_i(Δ'_i)`,   `e_i` = the lift of block `i` (`blockLift_lift`),

with `C_r = Σ_{i,b} V_{i,b}[r] · W_CRT[p_i + b]` independent of `Δ'`. This is `Claim4Hyp.tree_form`
with every tree known (the trees with a dead leaf are handled by `IsFixed`, `Bridge/Chain.lean`).

## The executable run is the committed response (`crtReconstruct_eq_resp`)

`convertToVoleAt_congr_key`: the columns depend on the leaf keys only off the hidden leaves. So if
the opening of a proof reconstructs the committed keys `K i j` at every non-hidden leaf (L1, the
binding of the leaf commitments: `hbind`), the verifier's whole CRT output (rows, masks, gate
hashes, lifted `Δ`) is the committed response `crtReconstructAt … (dbitOf Δ') … K` at
`Δ' = blocksOf (deltaBit Δ)`: a function of `Δ'` and the commitments only.
-/

open Finset

namespace VoleMole.Verifier.Bridge

-- The statements hold for any CTR PRG (`HasPrg`, `Verifier/Prg.lean`), AES included.
variable [VoleMole.Verifier.HasPrg]
set_option linter.unusedSectionVars false

open VoleMole.Arith VoleMole.Verifier

noncomputable section

/-! ## Words and bits -/

lemma u64_bit (x : UInt64) (s : ℕ) (hs : s < 64) :
    ((x >>> s.toUInt64) &&& 1 == 1) = x.toNat.testBit s := by
  have h1 : ((x >>> s.toUInt64) &&& 1).toNat = x.toNat / 2 ^ s % 2 := by
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
    simp [Nat.mod_eq_of_lt hs, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
  have key : ∀ y : UInt64, (y == 1) = decide (y.toNat = 1) := fun y => by
    by_cases hy : y = 1
    · subst hy; rfl
    · rw [beq_false_of_ne hy]
      exact (decide_eq_false fun h => hy (UInt64.toNat_inj.1 (h.trans rfl))).symm
  rw [Nat.testBit_eq_decide_div_mod_eq, key, h1]

lemma xorWords_size (a b : Array UInt64) : (xorWords a b).size = a.size := by
  simp [xorWords]

lemma xorWords_get (a b : Array UInt64) {w : ℕ} (hw : w < a.size) :
    (xorWords a b)[w]! = a[w]! ^^^ b[w]! := by
  simp [xorWords, hw, getElem!_pos]

lemma wbit_eq (w : Array UInt64) (r : ℕ) : wbit w r = (w[r / 64]!).toNat.testBit (r % 64) :=
  u64_bit _ _ (Nat.mod_lt _ (by norm_num))

lemma wbit_xorWords (a b : Array UInt64) {r : ℕ} (hr : r / 64 < a.size) :
    wbit (xorWords a b) r = (wbit a r ^^ wbit b r) := by
  rw [wbit_eq, wbit_eq, wbit_eq, xorWords_get a b hr, UInt64.toNat_xor, Nat.testBit_xor]

lemma wbit_zeroCol (p : Params) (r : ℕ) : wbit (zeroCol p) r = false := by
  rw [wbit_eq, zeroCol]
  by_cases h : r / 64 < p.colBytes / 8
  · simp [h, getElem!_pos]
  · simp [h]; exact Nat.zero_testBit _

lemma getElem!_range_map {α : Type} [Inhabited α] (n : ℕ) (f : ℕ → α) {b : ℕ} (hb : b < n) :
    ((Array.range n).map f)[b]! = f b := by
  simp [hb]

lemma getElem!_map' {α β : Type} [Inhabited α] [Inhabited β] (a : Array α) (g : α → β) {k : ℕ}
    (hk : k < a.size) : (a.map g)[k]! = g a[k]! := by
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_map, getElem!_pos a k hk]

/-- The rows `r < ℓ'` lie in every column. -/
lemma correctionRows_lt (p : Params) : p.correctionRows ≤ 64 * (p.colBytes / 8) := by
  simp only [Params.colBytes, Params.voleColBlocks, Params.voleRows]
  omega

lemma corrWords_size (p : Params) (i : ℕ) (corr : ByteArray) :
    p.colBytes / 8 ≤ (corrWords p i corr).size := by
  unfold corrWords
  split
  · simp [zeroCol]
  · simp only [wordsOf, Array.size_map, Array.size_range, ByteArray.size_append]
    refine Nat.div_le_div_right ?_
    show p.colBytes ≤ corr.size + (Array.replicate (p.colBytes - corr.size) (0 : UInt8)).size
    simp only [Array.size_replicate]; omega

/-! ## The hidden index -/

lemma foldl_pow_two (f : ℕ → Bool) (m : ℕ) :
    (List.range m).foldl (fun x d => if f d then x + 2 ^ d else x) 0 < 2 ^ m ∧
      ∀ b, ((List.range m).foldl (fun x d => if f d then x + 2 ^ d else x) 0).testBit b =
        (decide (b < m) && f b) := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨hlt, hbit⟩ := ih
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set x := (List.range m).foldl (fun x d => if f d then x + 2 ^ d else x) 0
    by_cases hf : f m
    · simp only [hf, ite_true]
      refine ⟨by rw [pow_succ]; omega, fun b => ?_⟩
      rw [add_comm]
      rcases lt_trichotomy b m with h | rfl | h
      · rw [Nat.testBit_two_pow_add_gt h, hbit]
        simp [h, show b < m + 1 by omega]
      · rw [Nat.testBit_two_pow_add_eq, hbit]
        simp [hf]
      · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by rw [pow_succ]; omega)
          (Nat.pow_le_pow_right (by norm_num) h))]
        simp; omega
    · simp only [hf, Bool.false_eq_true, ite_false]
      refine ⟨lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by omega)), fun b => ?_⟩
      rw [hbit]
      by_cases h : b = m
      · subst h; simp [hf]
      · by_cases h' : b < m <;> simp [h', show (b < m + 1) = (b < m) by
          apply propext; omega]

theorem hiddenIndex_lt (dbit : ℕ → Bool) (i : ℕ) : BAVC.hiddenIndex dbit i < 2 ^ BAVC.kOf i :=
  (foldl_pow_two _ _).1

theorem testBit_hiddenIndex (dbit : ℕ → Bool) (i : ℕ) {b : ℕ} (hb : b < BAVC.kOf i) :
    (BAVC.hiddenIndex dbit i).testBit b = dbit (BAVC.bitOffset i + b) := by
  rw [BAVC.hiddenIndex, (foldl_pow_two _ _).2]
  simp [hb]

/-! ## Columns -/

/-- The fold of `treeColumns`, bit by bit. -/
lemma foldl_xor_bit (cond : ℕ → Bool) (P : ℕ → Array UInt64) {r : ℕ} :
    ∀ (l : List ℕ) (acc : Array UInt64), r / 64 < acc.size →
      (l.foldl (fun acc j => if cond j then xorWords acc (P j) else acc) acc).size = acc.size ∧
      zb (wbit (l.foldl (fun acc j => if cond j then xorWords acc (P j) else acc) acc) r) =
        zb (wbit acc r) + (l.map fun j => zb (cond j && wbit (P j) r)).sum
  | [], acc, _ => by simp
  | j :: l, acc, hr => by
    rw [List.foldl_cons]
    by_cases hc : cond j
    · simp only [hc, ite_true]
      have hs := xorWords_size acc (P j)
      obtain ⟨h1, h2⟩ := foldl_xor_bit cond P l (xorWords acc (P j)) (hs ▸ hr)
      refine ⟨h1.trans hs, ?_⟩
      rw [h2, wbit_xorWords _ _ hr, zb_xor, List.map_cons, List.sum_cons]
      simp [hc, add_assoc]
    · simp only [hc, Bool.false_eq_true, ite_false]
      obtain ⟨h1, h2⟩ := foldl_xor_bit cond P l acc hr
      refine ⟨h1, ?_⟩
      rw [h2, List.map_cons, List.sum_cons]
      simp [hc]

/-- **ConvertToVOLE, one column, bit by bit**:
`q_{p_i+b}[r] = dI_b · c_i[r] + Σ_{j ≠ dI} (j ⊕ dI)_b · R_j[r]`. -/
theorem treeColumns_bit (p : Params) (iv : ByteArray) (i dI : ℕ) (corr : ByteArray)
    (key : ℕ → ByteArray) {b : ℕ} (hb : b < BAVC.kOf i) {r : ℕ} (hr : r < 64 * (p.colBytes / 8)) :
    zb (wbit (treeColumns p iv i dI corr key)[b]! r) =
      zb (dI.testBit b && wbit (corrWords p i corr) r) +
        ∑ j ∈ range (2 ^ BAVC.kOf i),
          zb (j != dI && (j ^^^ dI).testBit b && wbit (prgWords p iv i (key j)) r) := by
  unfold treeColumns
  rw [getElem!_range_map _ _ hb]
  have hacc : r / 64 < (if dI.testBit b then corrWords p i corr else zeroCol p).size := by
    have := corrWords_size p i corr
    split <;> simp [zeroCol] <;> omega
  rw [(foldl_xor_bit _ _ _ _ hacc).2, list_sum_range]
  congr 1
  · split <;> simp [wbit_zeroCol, *]
  · refine Finset.sum_congr rfl fun j hj => ?_
    by_cases hc : (j != dI && (j ^^^ dI).testBit b) = true
    · have hjd : j ≠ dI := by rintro rfl; simp at hc
      simp only [hc, Bool.true_and, prgOuts,
        getElem!_range_map _ _ (mem_range.1 hj), beq_false_of_ne hjd, Bool.false_eq_true,
        ite_false]
    · simp only [Bool.not_eq_true] at hc
      simp only [hc, Bool.false_and]

/-- The extractor's corrected small-VOLE value `u^{(i)} = c_i + Σ_j R_j` (row `r`), from the
committed keys `key j` of tree `i`. -/
def smallVoleU (p : Params) (iv : ByteArray) (i : ℕ) (corr : ByteArray) (key : ℕ → ByteArray)
    (r : ℕ) : ZMod 2 :=
  zb (wbit (corrWords p i corr) r) + ∑ j ∈ range (2 ^ BAVC.kOf i), zb (wbit (prgWords p iv i (key j)) r)

/-- `V_{i,b} = Σ_j j_b R_j` (row `r`), the `Δ`-independent part of column `p_i + b`. -/
def smallVoleV (p : Params) (iv : ByteArray) (i : ℕ) (key : ℕ → ByteArray) (b r : ℕ) : ZMod 2 :=
  ∑ j ∈ range (2 ^ BAVC.kOf i), zb (j.testBit b) * zb (wbit (prgWords p iv i (key j)) r)

/-- **ConvertToVOLE is affine in the hidden index**: `q_{p_i+b}[r] = V_{i,b}[r] + dI_b · u^{(i)}[r]`,
whatever `dI`. -/
theorem treeColumns_affine (p : Params) (iv : ByteArray) (i dI : ℕ) (corr : ByteArray)
    (key : ℕ → ByteArray) {b : ℕ} (hb : b < BAVC.kOf i) {r : ℕ} (hr : r < 64 * (p.colBytes / 8)) :
    zb (wbit (treeColumns p iv i dI corr key)[b]! r) =
      smallVoleV p iv i key b r + zb (dI.testBit b) * smallVoleU p iv i corr key r := by
  rw [treeColumns_bit p iv i dI corr key hb hr, smallVoleV, smallVoleU, zb_and, mul_add,
    Finset.mul_sum, ← add_assoc, add_comm _ (zb _ * zb _), add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j = dI
  · subst hj; simp; ring_nf; simp [show (2 : ZMod 2) = 0 from rfl]
  · have : (j != dI) = true := bne_iff_ne.2 hj
    simp [this, zb_and, Nat.testBit_xor, zb_xor]; ring

theorem convertToVoleAt_col (p : Params) (dbit : ℕ → Bool) (corr : ℕ → ByteArray)
    (iv : ByteArray) (key : ℕ → ℕ → ByteArray) {i b : ℕ} (hi : i < BAVC.tau) (hb : b < BAVC.kOf i) :
    (convertToVoleAt p dbit corr iv key)[BAVC.bitOffset i + b]! =
      (treeColumns p iv i (BAVC.hiddenIndex dbit i) (corr i) (key i))[b]! := by
  have hc := pos_lt hi hb
  unfold convertToVoleAt
  rw [getElem!_range_map _ _ (by omega)]
  simp only [hc, ite_true, treeOf_pos hb, Nat.add_sub_cancel_left]
  rw [getElem!_range_map _ _ hi]

/-! ## Rows -/

theorem rows_toGF (h5 : ByteArray → ByteArray) (p : Params) (dbit : ℕ → Bool)
    (cmult : ByteArray) (T : CrtTables) (iv : ByteArray) (cols : Array (Array UInt64)) {r : ℕ}
    (hr : r < p.correctionRows) :
    (crtReconstructAt h5 p dbit cmult T iv cols).rows[r]!.toGF =
      ∑ c ∈ range 120, if wbit cols[c]! r then liftCol T c else 0 := by
  simp only [crtReconstructAt, crtReconstructWith]
  rw [getElem!_range_map _ _ hr, rowMul_toGF]
  rfl

lemma bit_decide (x : ZMod 2) : SeedExtraction.bit (decide (x = 1)) = gf2 x := by
  rcases (by decide : ∀ y : ZMod 2, y = 0 ∨ y = 1) x with rfl | rfl <;>
    simp [SeedExtraction.bit]

/-- `u^{(i)}[r]` as a bit (`Claim4Hyp`'s `u`). -/
def uBit (p : Params) (iv : ByteArray) (corr : ℕ → ByteArray) (key : ℕ → ℕ → ByteArray)
    (i : Fin BAVC.tau) (r : ℕ) : Bool :=
  decide (smallVoleU p iv i (corr i) (key i) r = 1)

/-- The `Δ`-independent part `C_r = Σ_{i,b} V_{i,b}[r] · W_CRT[p_i + b]` of lifted row `r`. -/
def rowConst (T : CrtTables) (p : Params) (iv : ByteArray) (key : ℕ → ℕ → ByteArray) (r : ℕ) :
    GF128 :=
  ∑ i : Fin BAVC.tau, ∑ b : Fin (BAVC.kOf i),
    gf2 (smallVoleV p iv i (key i) b r) * liftCol T (BAVC.bitOffset i + b)

/-- **The lifted rows are affine per tree**:
`row_r = C_r + Σ_i u^{(i)}[r] · e_i(Δ'_i)` with `Δ' = blocksOf dbit` and `e = lift T`. -/
theorem resp_row (h5 : ByteArray → ByteArray) (T : CrtTables) (p : Params) (dbit : ℕ → Bool)
    (corr : ℕ → ByteArray) (cmult iv : ByteArray) (key : ℕ → ℕ → ByteArray) {r : ℕ}
    (hr : r < p.correctionRows) :
    (crtReconstructAt h5 p dbit cmult T iv (convertToVoleAt p dbit corr iv key)).rows[r]!.toGF =
      rowConst T p iv key r + ∑ i : Fin BAVC.tau, SeedExtraction.bit (uBit p iv corr key i r) *
        SeedExtraction.blockLift (lift T) i (blocksOf dbit i) := by
  have hr' := lt_of_lt_of_le hr (correctionRows_lt p)
  rw [rows_toGF _ _ _ _ _ _ _ hr, sum_range_120, rowConst, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [blockLift_lift, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [convertToVoleAt_col _ _ _ _ _ i.isLt b.isLt]
  have h := treeColumns_affine p iv i (BAVC.hiddenIndex dbit i) (corr i) (key i) b.isLt hr'
  rw [testBit_hiddenIndex _ _ b.isLt] at h
  have h2 : (if wbit (treeColumns p iv i (BAVC.hiddenIndex dbit i) (corr i) (key i))[(b : ℕ)]! r
      then liftCol T (BAVC.bitOffset i + b) else 0) =
      gf2 (zb (wbit (treeColumns p iv i (BAVC.hiddenIndex dbit i) (corr i) (key i))[(b : ℕ)]! r)) *
        liftCol T (BAVC.bitOffset i + b) := by
    rw [gf2_zb]; split <;> simp [SeedExtraction.bit, *]
  rw [h2, h, uBit, bit_decide, blocksOf]
  simp only [map_add, map_mul]
  ring

/-! ## The executable run is the committed response -/

theorem treeColumns_congr (p : Params) (iv : ByteArray) (i dI : ℕ) (corr : ByteArray)
    {key key' : ℕ → ByteArray} (h : ∀ j < 2 ^ BAVC.kOf i, j ≠ dI → key j = key' j) :
    treeColumns p iv i dI corr key = treeColumns p iv i dI corr key' := by
  have hp : prgOuts p iv i dI key = prgOuts p iv i dI key' := by
    unfold prgOuts
    refine Array.map_congr_left fun j hj => ?_
    have hj := Array.mem_range.1 hj
    by_cases hjd : j = dI
    · simp [hjd]
    · simp [hjd, h j hj hjd]
  unfold treeColumns
  rw [hp]

/-- The columns depend on the leaf keys only off the hidden leaves. -/
theorem convertToVoleAt_congr_key (p : Params) (dbit : ℕ → Bool) (corr : ℕ → ByteArray)
    (iv : ByteArray) {key key' : ℕ → ℕ → ByteArray}
    (h : ∀ i < BAVC.tau, ∀ j < 2 ^ BAVC.kOf i, j ≠ BAVC.hiddenIndex dbit i → key i j = key' i j) :
    convertToVoleAt p dbit corr iv key = convertToVoleAt p dbit corr iv key' := by
  have ht : ((Array.range BAVC.tau).map fun i =>
      treeColumns p iv i (BAVC.hiddenIndex dbit i) (corr i) (key i)) =
      (Array.range BAVC.tau).map fun i =>
        treeColumns p iv i (BAVC.hiddenIndex dbit i) (corr i) (key' i) :=
    Array.map_congr_left fun i hi =>
      treeColumns_congr _ _ _ _ _ (h i (Array.mem_range.1 hi))
  unfold convertToVoleAt
  rw [ht]

/-- `deltaBit Δ` is determined by the blocks it encodes. -/
theorem deltaBit_eq_dbitOf (delta : ByteArray) :
    BAVC.deltaBit delta = dbitOf (blocksOf (BAVC.deltaBit delta)) := by
  funext c
  by_cases hc : c < 120
  · exact (dbitOf_blocksOf _ hc).symm
  · rw [dbitOf_ge _ (by omega)]
    simp [BAVC.deltaBit, hc]

/-- The committed response at the blocks `Δ'`: the CRT output computed from the commitments
(`corrections`, `c_mult`, `iv`, the committed leaf keys `key`) and the gate-hash function `h5`
(`H₅`) alone. -/
def respAt (h5 : ByteArray → ByteArray) (T : CrtTables) (p : Params)
    (corrections cmult iv : ByteArray) (key : ℕ → ℕ → ByteArray) (Δ : Blocks) : CrtOut :=
  crtReconstructAt h5 p (dbitOf Δ) cmult T iv
    (convertToVoleAt p (dbitOf Δ) (fun i => corrections.extract ((i - 1) * p.correctionBytes)
      (i * p.correctionBytes)) iv key)

/-- **The verifier's CRT output at a proof is the committed response at its blocks**, if the
opening reconstructs the committed keys off the hidden leaves (L1). -/
theorem crtReconstruct_eq_respAt (Hs : Hashes) (T : CrtTables) (pf : Proof) (iv : ByteArray)
    (leaves : BAVC.Leaves) (key : ℕ → ℕ → ByteArray)
    (hbind : ∀ i < BAVC.tau, ∀ j < 2 ^ BAVC.kOf i, j ≠ BAVC.deltaIndex pf.delta i →
      leafKey leaves i j = key i j) :
    crtReconstruct Hs pf T iv (convertToVole pf iv leaves) =
      respAt (Hs.hash .h5) T pf.params pf.corrections pf.cmult iv key
        (blocksOf (BAVC.deltaBit pf.delta)) := by
  unfold crtReconstruct convertToVole respAt
  rw [← deltaBit_eq_dbitOf, convertToVoleAt_congr_key _ _ _ _ hbind]
  rfl

end

end VoleMole.Verifier.Bridge
