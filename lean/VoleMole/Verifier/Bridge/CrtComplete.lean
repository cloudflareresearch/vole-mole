import VoleMole.Verifier.Bridge.CrtCheck
import VoleMole.ZK.CMult
import VoleMole.ZK.TapeLemmas
import VoleMole.ZK.CrtMaskTables

/-!
# Bridge: CRT completeness (the verifier's CRT masks are a VOLE for the prover's commitment)

**`crtComplete`**: for faest-arch-opt's tables (`CrtGen.tables`), every parameter set whose 128
gate-label rows are corrected rows (`labelRowOffset + 128 ≤ ℓ'`: the five relations, both layouts)
and every `Δ`, the verifier's CRT masks on the prover's commitment are
`q_mask[m] = ṽ_mask[m] + u_mask[m] · Δ'` (`Bridge.CrtComplete`). The pieces, with `q` the
verifier's key columns and `v` the prover's tags:

* **Gate labels** (`tops_eq`, `gateInputs_eq`, `gateHashes_eq`): on the label rows
  `q_c = v_c + Δ_c · u` (`prover_column`), so `L_e(q) = L⁰_e + γ_e · u_pre` with `γ = Δ · G`
  (`zb_wbit_gammaOf`), and the verifier's gate hash `e` is the prover's `h^{γ_e}_e`.
* **`c_mult`** (`cmult_bit`, `u32_bit_any`): the verifier reads back bit `e` of row `m`,
  `(h⁰_e ⊕ h¹_e)_m ⊕ ⟨F[e], u_mask[m]⟩`, so its gate row is the prover's plus `γ_e ⟨F[e], u_mask[m]⟩`.
* **`r̃`** (`rowOf_bit`, `rTildeOf_bit`, `zb_polyMod_rTildeIn`, `polyMod_xor`, `tree_part`): on the
  uncorrected mask rows `q_c = v_c + Δ_c · u^{(i)}` (`prover_column_mask`); `polyMod` is linear
  and `r̃` is bilinear, so `W_tree · r̃(q)_m = W_tree · r̃(v)_m + Σ_c Δ_c · treeL_c`, `treeL_c` the CRT
  product of `Δ = e_c` with the mask's residues.
* **The identity** (`crt_core`): the mask's `u_low` bits are `⟨maskInv[k], u_mask⟩`
  (`formHom_maskInv`, from `ZK.maskInvOk_tables`) and `⟨F[e], ·⟩` is `Prover.dot` (`dot_eq_form`),
  so the tree and gate parts are `Σ_c Δ_c · L_c(u_mask)` with `CrtCheck.Lc`, and
  `L_c(a) = a · W_crt[c]` (`CrtCheck.Lc_eq`, the kernel-checked certificate).

`rTildeOf` and `polyMod` are folds over `List.range` (`Verifier/VOLE.lean`), the same computation
as the C++'s loops; the runners check them on all KAT proofs.
-/

open Finset

namespace VoleMole.Verifier.Bridge

open VoleMole.Arith VoleMole.Verifier

/-! ## Bits of blocks and words -/

lemma W128.bit_eq (a : W128) {j : ℕ} (hj : j < 128) :
    a.bit j = if j < 64 then a.lo.toNat.testBit j else a.hi.toNat.testBit (j - 64) := by
  unfold W128.bit
  split
  · exact u64_bit _ _ ‹_›
  · exact u64_bit _ _ (by omega)

lemma W128.bit_xor (a b : W128) {j : ℕ} (hj : j < 128) : (a.xor b).bit j = (a.bit j ^^ b.bit j) := by
  rw [W128.bit_eq _ hj, W128.bit_eq _ hj, W128.bit_eq _ hj]
  simp only [W128.xor, UInt64.toNat_xor, Nat.testBit_xor]
  split <;> rfl

lemma W128.bit_zero {j : ℕ} (hj : j < 128) : W128.zero.bit j = false := by
  rw [W128.bit_eq _ hj]; simp [W128.zero]

lemma toNat_one_shiftLeft {p : ℕ} (hp : p < 64) : ((1 : UInt64) <<< p.toUInt64).toNat = 2 ^ p := by
  rw [UInt64.toNat_shiftLeft]
  have : p.toUInt64.toNat % 64 = p := by simp [Nat.toUInt64]; omega
  rw [this, UInt64.toNat_one, Nat.one_shiftLeft, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hp)]

lemma W128.bit_single {p j : ℕ} (hp : p < 128) (hj : j < 128) :
    (W128.single p).bit j = decide (p = j) := by
  rw [W128.bit_eq _ hj]
  unfold W128.single
  split_ifs with h1 h2 h2
  · rw [toNat_one_shiftLeft h2, Nat.testBit_two_pow]
  · simp only [UInt64.toNat_zero, Nat.zero_testBit]; exact (decide_eq_false (by omega)).symm
  · simp only [UInt64.toNat_zero, Nat.zero_testBit]; exact (decide_eq_false (by omega)).symm
  · simp only [toNat_one_shiftLeft (show p - 64 < 64 by omega), Nat.testBit_two_pow]
    exact decide_eq_decide.2 ⟨fun h => by omega, fun h => by omega⟩

/-- Bit `b` of a word, as read by `place` and `polyMod`. -/
lemma u64_bit' (w : UInt64) {b : ℕ} (hb : b < 64) :
    ((w >>> b.toUInt64) &&& 1 == 1) = w.toNat.testBit b := u64_bit w b hb

lemma zb_ite_bool (c : Bool) (x : Bool) : zb (if c then x else false) = zb c * zb x := by
  cases c <;> simp

/-- **`place`**: bit `j` of `place w o k` is bit `j − o` of `w` for `o ≤ j < o + k`. -/
theorem W128.bit_place (w : UInt64) {o k j : ℕ} (hok : o + k ≤ 128) (hk : k ≤ 64) (hj : j < 128) :
    zb ((W128.place w o k).bit j) =
      ∑ b ∈ range k, zb (w.toNat.testBit b) * zb (decide (o + b = j)) := by
  have key : ∀ N, N ≤ k → zb (((List.range N).foldl (fun acc b =>
      if (w >>> b.toUInt64) &&& 1 == 1 then acc.xor (W128.single (o + b)) else acc) W128.zero).bit j) =
      ∑ b ∈ range N, zb (w.toNat.testBit b) * zb (decide (o + b = j)) := by
    intro N
    induction N with
    | zero => simp [W128.bit_zero hj]
    | succ N ih =>
      intro hN
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, sum_range_succ,
        ← ih (by omega), u64_bit' _ (by omega)]
      split
      · rename_i h
        rw [W128.bit_xor _ _ hj, zb_xor, W128.bit_single (by omega) hj, h]; simp
      · rename_i h
        simp only [Bool.not_eq_true] at h
        rw [h]; simp
  exact key k le_rfl

/-- **`r̃`, bit by bit**: bit `p_i + d` of `rTildeOf T src` is bit `d` of `rTildeIn src i mod M_i`. -/
theorem rTildeOf_bit (T : CrtTables) (src : Array W128) {j : ℕ} (hj : j < 120) :
    (rTildeOf T src).bit j = (polyMod (rTildeIn src (BAVC.treeOf j))
      T.mI[BAVC.treeOf j]!).toNat.testBit (j - BAVC.bitOffset (BAVC.treeOf j)) := by
  obtain ⟨hti, hle, hlt⟩ := treeOf_spec hj
  apply zb_inj
  have key : ∀ N, N ≤ BAVC.tau → zb (((List.range N).foldl (fun rt i => rt.xor (W128.place
      (polyMod (rTildeIn src i) T.mI[i]!) (BAVC.bitOffset i) (BAVC.kOf i))) W128.zero).bit j) =
      if BAVC.treeOf j < N then zb ((polyMod (rTildeIn src (BAVC.treeOf j))
        T.mI[BAVC.treeOf j]!).toNat.testBit (j - BAVC.bitOffset (BAVC.treeOf j))) else 0 := by
    intro N
    induction N with
    | zero => intro _; simp [W128.bit_zero (show j < 128 by omega)]
    | succ N ih =>
      intro hN
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        W128.bit_xor _ _ (by omega), zb_xor, ih (by omega)]
      have hpl := pos_lt (show N < BAVC.tau by omega) (show BAVC.kOf N - 1 < BAVC.kOf N by
        rw [kOf_eq]; split <;> omega)
      have hk : BAVC.kOf N ≤ 64 := by rw [kOf_eq]; split <;> omega
      rw [W128.bit_place _ (by omega) hk (by omega)]
      by_cases hN' : BAVC.treeOf j = N
      · subst hN'
        simp only [lt_irrefl, ↓reduceIte, zero_add, show BAVC.treeOf j < BAVC.treeOf j + 1 by omega]
        rw [Finset.sum_eq_single (j - BAVC.bitOffset (BAVC.treeOf j))]
        · simp [show BAVC.bitOffset (BAVC.treeOf j) + (j - BAVC.bitOffset (BAVC.treeOf j)) = j by omega]
        · intro b _ hb
          simp [show BAVC.bitOffset (BAVC.treeOf j) + b ≠ j by omega]
        · intro h; exact absurd (Finset.mem_range.2 hlt) h
      · have hsum : ∑ b ∈ range (BAVC.kOf N), zb ((polyMod (rTildeIn src N) T.mI[N]!).toNat.testBit b) *
            zb (decide (BAVC.bitOffset N + b = j)) = 0 := by
          refine Finset.sum_eq_zero fun b hb => ?_
          have hb := Finset.mem_range.1 hb
          have : BAVC.bitOffset N + b ≠ j := by
            intro e
            have := pos_inj hb hlt (show BAVC.bitOffset N + b =
              BAVC.bitOffset (BAVC.treeOf j) + (j - BAVC.bitOffset (BAVC.treeOf j)) by omega)
            exact hN' this.1.symm
          simp [this]
        rw [hsum, add_zero]
        by_cases h : BAVC.treeOf j < N
        · simp [h, show BAVC.treeOf j < N + 1 by omega]
        · simp [h, show ¬ BAVC.treeOf j < N + 1 by omega]
  rw [rTildeOf, key _ le_rfl]
  simp [hti]

/-! ## `polyMod` is linear -/

lemma polyMod_step_xor (K : UInt64) (deg b : ℕ) (hb : b < 64) (x y : UInt64) :
    (if decide (b ≥ deg) && (x ^^^ y) >>> b.toUInt64 &&& 1 == 1 then x ^^^ y ^^^ K else x ^^^ y) =
      (if decide (b ≥ deg) && x >>> b.toUInt64 &&& 1 == 1 then x ^^^ K else x) ^^^
        (if decide (b ≥ deg) && y >>> b.toUInt64 &&& 1 == 1 then y ^^^ K else y) := by
  rw [u64_bit' _ hb, u64_bit' _ hb, u64_bit' _ hb, UInt64.toNat_xor, Nat.testBit_xor]
  have ext : ∀ a b : UInt64, (∀ i, a.toNat.testBit i = b.toNat.testBit i) → a = b :=
    fun a b h => UInt64.toNat_inj.1 (Nat.eq_of_testBit_eq h)
  cases decide (b ≥ deg) <;> cases x.toNat.testBit b <;> cases y.toNat.testBit b <;>
    simp only [Bool.false_and, Bool.true_and, Bool.xor_false, Bool.xor_true, Bool.not_true,
      Bool.not_false, Bool.false_eq_true, ↓reduceIte] <;>
    refine ext _ _ fun i => ?_ <;>
    simp only [UInt64.toNat_xor, Nat.testBit_xor] <;>
    cases x.toNat.testBit i <;> cases y.toNat.testBit i <;> cases K.toNat.testBit i <;> rfl

/-- **`polyMod` is additive** (each reduction step adds `M_i X^s` iff a bit is set). -/
theorem polyMod_xor (x y m : UInt64) : polyMod (x ^^^ y) m = polyMod x m ^^^ polyMod y m := by
  simp only [polyMod]
  generalize m.toNat.log2 = deg
  have key : ∀ (l : List ℕ), (∀ s ∈ l, s < 64) → ∀ x y : UInt64,
      l.foldl (fun x s => if decide (63 - s ≥ deg) && x >>> (63 - s).toUInt64 &&& 1 == 1 then
        x ^^^ m <<< (63 - s - deg).toUInt64 else x) (x ^^^ y) =
      l.foldl (fun x s => if decide (63 - s ≥ deg) && x >>> (63 - s).toUInt64 &&& 1 == 1 then
        x ^^^ m <<< (63 - s - deg).toUInt64 else x) x ^^^
      l.foldl (fun x s => if decide (63 - s ≥ deg) && x >>> (63 - s).toUInt64 &&& 1 == 1 then
        x ^^^ m <<< (63 - s - deg).toUInt64 else x) y := by
    intro l
    induction l with
    | nil => intros; rfl
    | cons s l ih =>
      intro hl x y
      simp only [List.foldl_cons]
      rw [polyMod_step_xor (m <<< (63 - s - deg).toUInt64) deg (63 - s) (by omega) x y]
      exact ih (fun s' hs' => hl s' (by simp [hs'])) _ _
  exact key _ (fun s hs => List.mem_range.1 hs) x y

lemma polyMod_zero (m : UInt64) : polyMod 0 m = 0 := by
  simp only [polyMod]
  generalize m.toNat.log2 = deg
  induction (List.range 64) with
  | nil => rfl
  | cons s l ih =>
    simp only [List.foldl_cons]
    rw [u64_bit' _ (by omega)]
    simpa using ih

/-! ## `r̃` as a bilinear form -/

/-- `Σ_{a ∈ l} f a` over words (XOR). -/
def xs64 (l : List ℕ) (f : ℕ → UInt64) : UInt64 := l.foldl (fun acc a => acc ^^^ f a) 0

lemma foldl_xor64_start (f : ℕ → UInt64) : ∀ (l : List ℕ) (x : UInt64),
    l.foldl (fun acc a => acc ^^^ f a) x = x ^^^ l.foldl (fun acc a => acc ^^^ f a) 0
  | [], x => by simp
  | a :: l, x => by
    simp only [List.foldl_cons]
    rw [foldl_xor64_start f l (x ^^^ f a), foldl_xor64_start f l (0 ^^^ f a), UInt64.zero_xor,
      UInt64.xor_assoc]

lemma xs64_cons (a : ℕ) (l : List ℕ) (f : ℕ → UInt64) : xs64 (a :: l) f = f a ^^^ xs64 l f := by
  simp only [xs64, List.foldl_cons, UInt64.zero_xor]
  exact foldl_xor64_start f l (f a)

lemma map_xs64 (φ : UInt64 → UInt64) (h0 : φ 0 = 0) (hx : ∀ x y, φ (x ^^^ y) = φ x ^^^ φ y)
    (l : List ℕ) (f : ℕ → UInt64) : φ (xs64 l f) = xs64 l (fun a => φ (f a)) := by
  induction l with
  | nil => exact h0
  | cons a l ih => rw [xs64_cons, xs64_cons, hx, ih]

lemma zb_xs64 (l : List ℕ) (f : ℕ → UInt64) (d : ℕ) :
    zb ((xs64 l f).toNat.testBit d) = (l.map fun a => zb ((f a).toNat.testBit d)).sum := by
  induction l with
  | nil => simp [xs64]
  | cons a l ih => rw [xs64_cons, UInt64.toNat_xor, Nat.testBit_xor, zb_xor, ih]; simp

lemma bitsAt_eq (a : W128) (o k : ℕ) :
    a.bitsAt o k = xs64 (List.range k) fun b => if a.bit (o + b) then (1 : UInt64) <<< b.toUInt64
      else 0 := by
  simp only [W128.bitsAt, xs64]
  refine List.foldl_ext _ _ _ fun acc b _ => ?_
  split <;> simp

lemma one_shiftLeft_shiftLeft {b t : ℕ} (h : b + t < 64) :
    ((1 : UInt64) <<< b.toUInt64) <<< t.toUInt64 = (1 : UInt64) <<< (b + t).toUInt64 := by
  apply UInt64.toNat_inj.1
  rw [toNat_one_shiftLeft h, UInt64.toNat_shiftLeft, toNat_one_shiftLeft (by omega)]
  have : t.toUInt64.toNat % 64 = t := by simp [Nat.toUInt64]; omega
  rw [this, Nat.shiftLeft_eq, ← pow_add, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) h)]

/-- **`r̃` is bilinear**: bit `d` of `rTildeIn src i mod M` is
`Σ_{t, b < k_i} src[t]_{p_i + b} · (X^{b+t} mod M)_d`. -/
theorem zb_polyMod_rTildeIn (src : Array W128) (i : ℕ) (M : UInt64) (d : ℕ)
    (hk : BAVC.kOf i ≤ 8) :
    zb ((polyMod (rTildeIn src i) M).toNat.testBit d) =
      ∑ t ∈ range (BAVC.kOf i), ∑ b ∈ range (BAVC.kOf i),
        zb (src[t]!.bit (BAVC.bitOffset i + b)) *
          zb ((polyMod ((1 : UInt64) <<< (b + t).toUInt64) M).toNat.testBit d) := by
  have hr : rTildeIn src i = xs64 (List.range (BAVC.kOf i)) fun t =>
      xs64 (List.range (BAVC.kOf i)) fun b => if src[t]!.bit (BAVC.bitOffset i + b) then
        (1 : UInt64) <<< (b + t).toUInt64 else 0 := by
    simp only [rTildeIn]
    refine List.foldl_ext _ _ _ fun x t ht => ?_
    have ht := List.mem_range.1 ht
    congr 1
    rw [bitsAt_eq, map_xs64 (· <<< t.toUInt64) (by simp) (fun _ _ => UInt64.shiftLeft_xor)]
    simp only [xs64]
    refine List.foldl_ext _ _ _ fun y b hb => ?_
    have hb := List.mem_range.1 hb
    split
    · rw [one_shiftLeft_shiftLeft (by omega)]
    · simp
  rw [hr, map_xs64 (polyMod · M) (polyMod_zero M) (fun x y => polyMod_xor x y M), zb_xs64,
    list_sum_range]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_xs64 (polyMod · M) (polyMod_zero M) (fun x y => polyMod_xor x y M), zb_xs64,
    list_sum_range]
  refine Finset.sum_congr rfl fun b _ => ?_
  split
  · rename_i h; rw [h, zb_true, one_mul]
  · rename_i h; simp only [Bool.not_eq_true] at h; rw [h, polyMod_zero]; simp

/-! ## Rows of the key matrix -/

lemma orFold_testBit (f : ℕ → Bool) : ∀ N, N ≤ 64 → ∀ j,
    ((List.range N).foldl (fun (acc : UInt64) c => if f c then acc ||| (1 : UInt64) <<< c.toUInt64
      else acc) 0).toNat.testBit j = (decide (j < N) && f j) := by
  intro N
  induction N with
  | zero => intro _ j; simp
  | succ N ih =>
    intro hN j
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    split
    · rename_i h
      rw [UInt64.toNat_or, Nat.testBit_or, ih (by omega), toNat_one_shiftLeft (by omega),
        Nat.testBit_two_pow]
      by_cases hj : j = N
      · subst hj; simp [h]
      · by_cases hj' : j < N
        · simp [hj', show j < N + 1 by omega, Ne.symm hj]
        · simp [hj', show ¬ j < N + 1 by omega, Ne.symm hj]
    · rename_i h
      rw [ih (by omega)]
      by_cases hj : j = N
      · subst hj; simp [h]
      · by_cases hj' : j < N
        · simp [hj', show j < N + 1 by omega]
        · simp [hj', show ¬ j < N + 1 by omega]

/-- Bit `c` of row `r` of the key matrix is bit `r` of column `c`. -/
theorem rowOf_bit (cols : Array (Array UInt64)) (r : ℕ) {c : ℕ} (hc : c < 128) :
    (rowOf cols r).bit c = wbit cols[c]! r := by
  have hfold : rowOf cols r =
      ⟨(List.range 64).foldl (fun (acc : UInt64) c => if wbit cols[c]! r then
          acc ||| (1 : UInt64) <<< c.toUInt64 else acc) 0,
        (List.range 64).foldl (fun (acc : UInt64) c => if wbit cols[c + 64]! r then
          acc ||| (1 : UInt64) <<< c.toUInt64 else acc) 0⟩ := by
    unfold rowOf
    simp only [Id.run]
    rw [forIn_range_foldl _ _ _ (fun c (x : UInt64 × UInt64) =>
      (if wbit cols[c]! r then x.1 ||| (1 : UInt64) <<< c.toUInt64 else x.1,
       if wbit cols[c + 64]! r then x.2 ||| (1 : UInt64) <<< c.toUInt64 else x.2))
      fun c x => by split_ifs <;> rfl]
    have key : ∀ (l : List ℕ) (x : UInt64 × UInt64), l.foldl (fun x c =>
        (if wbit cols[c]! r then x.1 ||| (1 : UInt64) <<< c.toUInt64 else x.1,
         if wbit cols[c + 64]! r then x.2 ||| (1 : UInt64) <<< c.toUInt64 else x.2)) x =
        (l.foldl (fun (acc : UInt64) c => if wbit cols[c]! r then
          acc ||| (1 : UInt64) <<< c.toUInt64 else acc) x.1,
         l.foldl (fun (acc : UInt64) c => if wbit cols[c + 64]! r then
          acc ||| (1 : UInt64) <<< c.toUInt64 else acc) x.2) := by
      intro l
      induction l with
      | nil => intro x; rfl
      | cons c l ih => intro x; rw [List.foldl_cons, ih]; rfl
    rw [key]
    simp only [pure_bind]
    rfl
  rw [hfold, W128.bit_eq _ hc]
  simp only
  split
  · rw [orFold_testBit _ 64 le_rfl]; simp [‹c < 64›]
  · rw [orFold_testBit _ 64 le_rfl]; simp [show c - 64 < 64 by omega, show c - 64 + 64 = c by omega]

/-! ## The prover's columns on the mask rows -/

/-- Below the corrected rows the correction is zero. -/
lemma wbit_corrWords_high (p : Params) (iv : ByteArray) (key : ℕ → ℕ → ByteArray) (i : ℕ) {r : ℕ}
    (hr : p.correctionRows ≤ r) : wbit (corrWords p i (proverCorr p iv key i)) r = false := by
  unfold corrWords
  split
  · exact wbit_zeroCol p r
  · have hu : (proverU p iv key 0).size = p.colBytes / 8 := by
      rw [proverU]
      exact (smallVoleUWords_spec p iv 0 (key 0) (r := 0) (by
        simp only [Params.colBytes, Params.voleColBlocks, Params.voleRows, Params.nMask]; omega)).1
    have hcs : (proverCorr p iv key i).size = p.correctionBytes :=
      correctionOf_size p _ _ hu
    have hcb := correctionBytes_mul p
    rw [wbit_eq]
    by_cases h : r / 64 < (wordsOf (proverCorr p iv key i ++
        ⟨Array.replicate (p.colBytes - (proverCorr p iv key i).size) 0⟩)).size
    · rw [← wbit_eq, wbit_wordsOf _ (by simpa [wordsOf] using h), ZK.Sim.get!_append]
      simp only [show ¬ r / 8 < (proverCorr p iv key i).size by rw [hcs]; omega, ↓reduceIte]
      have : ({ data := Array.replicate (p.colBytes - (proverCorr p iv key i).size) 0 } :
          ByteArray) = Prover.zeros _ := rfl
      rw [this, ZK.Sim.get!_zeros]; simp
    · rw [getElem!_neg (wordsOf _) _ h]
      exact Nat.zero_testBit _

/-- **The prover's VOLE correlation on the mask rows** (uncorrected): column `p_i + b` of the
verifier's keys is the prover's tag column plus `Δ_{p_i+b} · u^{(i)}`. -/
theorem prover_column_mask (p : Params) (iv : ByteArray) (key : ℕ → ℕ → ByteArray)
    (dbit : ℕ → Bool) {i b r : ℕ} (hi : i < BAVC.tau) (hb : b < BAVC.kOf i)
    (hr1 : p.correctionRows ≤ r) (hr2 : r < 64 * (p.colBytes / 8)) :
    wbit (convertToVoleAt p dbit (proverCorr p iv key) iv key)[BAVC.bitOffset i + b]! r =
      (wbit (Prover.senderColumns p iv key)[BAVC.bitOffset i + b]! r ^^
        (dbit (BAVC.bitOffset i + b) && wbit (proverU p iv key i) r)) := by
  have hU : smallVoleU p iv i (proverCorr p iv key i) (key i) r =
      zb (wbit (proverU p iv key i) r) := by
    rw [smallVoleU, wbit_corrWords_high p iv key i hr1, zb_false, zero_add, proverU,
      (smallVoleUWords_spec p iv i (key i) (by omega)).2]
  apply zb_inj
  rw [convertToVoleAt_col _ _ _ _ _ hi hb, Prover.senderColumns,
    convertToVoleAt_col _ _ _ _ _ hi hb,
    zb_xor, zb_and, treeColumns_affine _ _ _ _ _ _ hb hr2, treeColumns_affine _ _ _ _ _ _ hb hr2,
    testBit_hiddenIndex _ _ hb, testBit_hiddenIndex _ _ hb, hU]
  simp [zb]

/-! ## The tables as numbers -/

lemma tables_wTree : CrtGen.tables.wTree =
    (Array.range 120).map fun j => CrtGen.w128OfNat (CrtGen.transposeRow CrtGen.wTree j) := rfl
lemma tables_wGate : CrtGen.tables.wGate =
    (Array.range 312).map fun e => CrtGen.w128OfNat (CrtGen.transposeRow CrtGen.wGate e) := rfl
lemma tables_wCrt : CrtGen.tables.wCrt =
    (Array.range 120).map fun j => CrtGen.w128OfNat (CrtGen.transposeRow CrtGen.wCrt j) := rfl
lemma tables_g : CrtGen.tables.g = (Array.range 120).map fun j =>
    (Array.range 5).map fun w => (CrtGen.transposeRow CrtGen.G j / 2 ^ (64 * w) % 2 ^ 64).toUInt64 :=
  rfl
lemma tables_mI : CrtGen.tables.mI = CrtGen.moduli.map Nat.toUInt64 := rfl

lemma transposeRow_eq (M : Array ℕ) (j : ℕ) : CrtGen.transposeRow M j = CrtCheck.trRow M.toList j := by
  rw [CrtGen.transposeRow, CrtCheck.trRow, ← Array.foldl_toList]

open CrtCheck in
lemma wTree_toGF {j : ℕ} (hj : j < 120) : CrtGen.tables.wTree[j]!.toGF = natGF (wtL.getD j 0) := by
  rw [tables_wTree, getElem!_range_map _ _ hj, List.getD_eq_getElem?_getD, wtL, List.getElem?_map,
    List.getElem?_range hj, transposeRow_eq]
  rfl

open CrtCheck in
lemma wGate_toGF {e : ℕ} (he : e < 312) :
    CrtGen.tables.wGate[e]!.toGF = natGF (trRow CrtGen.wGate.toList e) := by
  rw [tables_wGate, getElem!_range_map _ _ he, transposeRow_eq]; rfl

open CrtCheck in
lemma liftCol_tables {c : ℕ} (hc : c < 120) : liftCol CrtGen.tables c = natGF (wcL.getD c 0) := by
  rw [liftCol, tables_wCrt, getElem!_range_map _ _ hc, wcL_getD hc, transposeRow_eq]; rfl

open CrtCheck in
lemma wbit_g_tables {c e : ℕ} (hc : c < 120) (he : e < 320) :
    wbit CrtGen.tables.g[c]! e = (trRow CrtGen.G.toList c).testBit e := by
  rw [tables_g, getElem!_range_map _ _ hc, wbit_eq, getElem!_range_map _ _ (by omega),
    ← transposeRow_eq]
  simp only [Nat.toUInt64, UInt64.toNat_ofNat', Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    Nat.mod_mod, show e % 64 < 64 from Nat.mod_lt _ (by norm_num), decide_true, Bool.true_and]
  rw [show e % 64 + 64 * (e / 64) = e by omega]

open CrtCheck in
lemma fRows_get {e : ℕ} (he : e < 312) :
    Prover.fRows[e]! = CrtGen.w128OfNat (CrtGen.F.toList.getD e 0) := by
  have h312 : e < CrtGen.F.size := by
    have := F_length; rw [Array.length_toList] at this; omega
  rw [Prover.fRows, getElem!_map' _ _ h312, List.getD_eq_getElem?_getD, Array.getElem?_toList,
    getElem!_pos CrtGen.F e h312, Array.getElem?_eq_getElem h312]
  rfl

open CrtCheck in
lemma pmVal_eq {i s : ℕ} (hi : i < 17) (hs : s < 16) :
    pmVal i s = (polyMod ((1 : UInt64) <<< s.toUInt64) CrtGen.tables.mI[i]!).toNat := by
  have h17 : i < CrtGen.moduli.size := by
    have : CrtGen.moduli.size = 17 := by decide +kernel
    omega
  have hm : CrtGen.tables.mI[i]! = (CrtGen.moduli.getD i 0).toUInt64 := by
    rw [tables_mI, getElem!_map' _ _ h17, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h17,
      getElem!_pos _ i h17]
    rfl
  have e1 : pmTab.getD i [] = (List.range 16).map fun s =>
      (polyMod ((1 : UInt64) <<< s.toUInt64) (CrtGen.moduli.getD i 0).toUInt64).toNat := by
    rw [pmTab, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl
  rw [hm, pmVal, e1, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hs]
  rfl

/-! ## `⟨F[e], u_mask⟩` and the mask's `u_low` bits as linear forms -/

lemma and_one_beq (v : UInt64) : (v &&& 1 == 1) = v.toNat.testBit 0 := by
  have := u64_bit v 0 (by norm_num)
  rwa [show (0 : ℕ).toUInt64 = 0 from rfl, UInt64.shiftRight_zero] at this

lemma parStep_toNat (v : UInt64) {k : ℕ} (hk : k < 64) :
    (v ^^^ (v >>> k.toUInt64)).toNat = parStep k v.toNat := by
  rw [UInt64.toNat_xor, UInt64.toNat_shiftRight, parStep]
  congr 2
  simp [Nat.toUInt64]; omega

lemma foldl_parStep_toNat : ∀ (l : List ℕ), (∀ s ∈ l, s < 64) → ∀ v : UInt64,
    (l.foldl (fun v (s : ℕ) => v ^^^ v >>> s.toUInt64) v).toNat =
      l.foldl (fun n s => parStep s n) v.toNat
  | [], _, _ => rfl
  | s :: l, hl, v => by
    simp only [List.foldl_cons]
    rw [foldl_parStep_toNat l (fun s' hs' => hl s' (by simp [hs'])), parStep_toNat _ (hl s (by simp))]

lemma parity64_eq (x : UInt64) : Prover.parity64 x = par x.toNat := by
  have hx := x.toNat_lt
  have h64 : parStep 64 x.toNat = x.toNat := by
    rw [parStep, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hx, Nat.xor_zero]
  unfold Prover.parity64
  simp only [Id.run]
  rw [List.forIn_pure_yield_eq_foldl]
  show (List.foldl (fun v (s : ℕ) => v ^^^ v >>> s.toUInt64) x [32, 16, 8, 4, 2, 1] &&& 1 == 1) = _
  rw [and_one_beq, foldl_parStep_toNat _ (by decide), par, h64]
  rfl

/-- **`dot` is the linear form of its first argument.** -/
theorem dot_eq_form (l : ℕ) (w : W128) : Prover.dot (CrtGen.w128OfNat l) w = form l w.toGF := by
  rw [Prover.dot, parity64_eq, UInt64.toNat_xor, par_xor, form]
  simp only [CrtGen.w128OfNat, W128.toGF, UInt64.toNat_and, Nat.toUInt64, UInt64.toNat_ofNat',
    Nat.mod_mod]
  congr 2
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_and, Nat.testBit_mod_two_pow]
  by_cases hj : j < 64
  · simp [hj]
  · simp [hj, Nat.testBit_lt_two_pow (lt_of_lt_of_le w.hi.toNat_lt
      (Nat.pow_le_pow_right (by norm_num) (show 64 ≤ j by omega)))]

/-- **The `u_low` bits of a mask are read back by `maskInv`**: for the mask
`W_CRT · low ⊕ M_tree · h` (`compute_u_mask`) and `k < 120`, `⟨maskInv[k], mask⟩ = low_k`. -/
theorem formHom_maskInv (low : ℕ → Bool) (h : UInt8) {k : ℕ} (hk : k < 120) :
    formHom (ZK.maskInv.getD k 0) (((W128.rowMul low 120 CrtGen.tables.wCrt).xor
      (CrtGen.w128OfNat (CrtGen.pmul h.toNat Prover.mTree))).toGF) = zb (low k) := by
  have hT := ZK.maskInvOk_tables
  have hf : ∀ c < 128, formHom (ZK.maskInv.getD k 0) (ZK.maskCol CrtGen.tables c) =
      zb (c == k) := by
    intro c hc
    show zb _ = _
    congr 1
    simp only [ZK.maskInvOk, List.all_eq_true, List.mem_range, beq_iff_eq] at hT
    simpa using hT k (by omega) c hc
  rw [toGF_xor, rowMul_toGF, ZK.pmul_byte, ZK.toGF_w128OfNat_foldl, ZK.w128OfNat_zero_toGF,
    zero_add, map_add, map_sum, list_sum_range, map_sum]
  have hcol : ∀ c < 120, (if low c then CrtGen.tables.wCrt[c]!.toGF else 0) =
      (if low c then ZK.maskCol CrtGen.tables c else 0) := fun c hc => by
    rw [ZK.maskCol]; simp only [hc, ↓reduceIte]
  rw [Finset.sum_eq_single k (fun c hc hck => by
      have hc' := Finset.mem_range.1 hc
      rw [hcol c hc']
      split
      · rw [hf c (by omega), beq_false_of_ne hck]; rfl
      · exact map_zero _)
    (fun h' => absurd (Finset.mem_range.2 hk) h')]
  rw [Finset.sum_eq_zero fun j hj => by
    have hj := Finset.mem_range.1 hj
    have hmc : (CrtGen.w128OfNat (if h.toNat.testBit j then CrtGen.pmul (2 ^ j) Prover.mTree
        else 0)).toGF = if h.toNat.testBit j then ZK.maskCol CrtGen.tables (120 + j) else 0 := by
      split
      · rw [ZK.maskCol]; simp only [show ¬ 120 + j < 120 by omega, ↓reduceIte, Nat.add_sub_cancel_left]
      · rfl
    rw [hmc]
    split
    · rw [hf _ (by omega), beq_false_of_ne (show 120 + j ≠ k by omega)]; rfl
    · exact map_zero _]
  rw [add_zero, hcol k hk]
  split
  · rw [hf k (by omega)]; simp_all
  · simp_all

/-! ## The gate hashes and `c_mult` -/

/-- Bit `e` of `γ = Δ · G`. -/
lemma zb_wbit_gammaOf (T : CrtTables) (dbit : ℕ → Bool) {e : ℕ} (he : e < 320) :
    zb (wbit (gammaOf T dbit) e) = ∑ c ∈ range 120, zb (dbit c && wbit T.g[c]! e) := by
  rw [gammaOf, (foldl_xor_bit dbit (fun c => T.g[c]!) _ _ (by simp; omega)).2, list_sum_range]
  have : wbit (Array.replicate 5 (0 : UInt64)) e = false := by
    rw [wbit_eq]
    by_cases h : e / 64 < 5
    · simp [h]
    · rw [getElem!_neg _ _ (by simpa using h)]; exact Nat.zero_testBit _
  rw [this, zb_false, zero_add]

lemma gammaOf_false (T : CrtTables) {e : ℕ} (he : e < 320) :
    wbit (gammaOf T fun _ => false) e = false := by
  apply zb_inj
  rw [zb_wbit_gammaOf _ _ he]; simp

lemma W128.ext_toGF {a b : W128} (h : a.toGF = b.toGF) : a = b := by
  cases a; cases b
  simp only [W128.toGF, GF128.mk.injEq] at h
  rw [h.1, h.2]

lemma toGF_ite (P : Prop) [Decidable P] (a : W128) :
    (if P then a else W128.zero).toGF = if P then a.toGF else 0 := by
  split <;> rfl

/-- The label rows of the verifier's key columns: `q_c = v_c + Δ_c · u` (as 128-bit blocks). -/
lemma tops_eq (p : Params) (iv : ByteArray) (key : ℕ → ℕ → ByteArray) (dbit : ℕ → Bool)
    (hlab : p.labelRowOffset + 128 ≤ p.correctionRows) {c : ℕ} (hc : c < 120) :
    (⟨wordAt (convertToVoleAt p dbit (proverCorr p iv key) iv key)[c]! p.labelRowOffset,
      wordAt (convertToVoleAt p dbit (proverCorr p iv key) iv key)[c]! (p.labelRowOffset + 64)⟩ :
      W128).toGF =
    (⟨wordAt (Prover.senderColumns p iv key)[c]! p.labelRowOffset,
      wordAt (Prover.senderColumns p iv key)[c]! (p.labelRowOffset + 64)⟩ : W128).toGF +
    (if dbit c then (⟨wordAt (proverU p iv key 0) p.labelRowOffset,
      wordAt (proverU p iv key 0) (p.labelRowOffset + 64)⟩ : W128).toGF else 0) := by
  obtain ⟨hi, hle, hb⟩ := treeOf_spec hc
  have hcc : c = BAVC.bitOffset (BAVC.treeOf c) + (c - BAVC.bitOffset (BAVC.treeOf c)) := by omega
  have hw : ∀ o, o + 64 ≤ p.labelRowOffset + 128 →
      wordAt (convertToVoleAt p dbit (proverCorr p iv key) iv key)[c]! o =
        wordAt (Prover.senderColumns p iv key)[c]! o ^^^
          (if dbit c then wordAt (proverU p iv key 0) o else 0) := by
    intro o ho
    apply UInt64.toNat_inj.1
    apply Nat.eq_of_testBit_eq
    intro s
    by_cases hs : s < 64
    · rw [UInt64.toNat_xor, Nat.testBit_xor, ZK.Sim.wordAt_testBit _ _ hs,
        ZK.Sim.wordAt_testBit _ _ hs, hcc, prover_column p iv key dbit hi hb (by omega), ← hcc]
      by_cases hd : dbit c
      · simp only [hd, Bool.true_and, ↓reduceIte]; rw [ZK.Sim.wordAt_testBit _ _ hs]
      · simp only [hd, Bool.false_and, Bool.false_eq_true, ↓reduceIte, UInt64.toNat_zero,
          Nat.zero_testBit]
    · rw [ZK.Sim.uint64_testBit_lt _ (by omega), ZK.Sim.uint64_testBit_lt _ (by omega)]
  rw [hw _ (by omega), hw _ (by omega)]
  split <;> rfl

/-- **The verifier's gate inputs are the prover's at `L^{γ_e}_e`.** -/
lemma gateInputs_eq (p : Params) (iv : ByteArray) (key : ℕ → ℕ → ByteArray) (dbit : ℕ → Bool)
    (hlab : p.labelRowOffset + 128 ≤ p.correctionRows) {e : ℕ} (he : e < 312) :
    (gateInputs p CrtGen.tables iv (convertToVoleAt p dbit (proverCorr p iv key) iv key))[e]? =
      (Prover.gateInputsOff p CrtGen.tables iv (Prover.senderColumns p iv key)
        (if wbit (gammaOf CrtGen.tables dbit) e then
          ⟨wordAt (proverU p iv key 0) p.labelRowOffset,
            wordAt (proverU p iv key 0) (p.labelRowOffset + 64)⟩ else W128.zero))[e]? := by
  simp only [gateInputs, Prover.gateInputsOff, List.getElem?_map, List.getElem?_range
    (show e < p.nMult from he), Option.map_some, Option.some.injEq]
  congr 3
  apply W128.ext_toGF
  rw [toGF_xor, rowMul_toGF, rowMul_toGF, toGF_ite]
  rw [Finset.sum_congr rfl fun c hc => by
    rw [getElem!_range_map _ _ (Finset.mem_range.1 hc), tops_eq p iv key dbit hlab
      (Finset.mem_range.1 hc), ← getElem!_range_map _ (fun c => (⟨wordAt
        (Prover.senderColumns p iv key)[c]! p.labelRowOffset, wordAt
        (Prover.senderColumns p iv key)[c]! (p.labelRowOffset + 64)⟩ : W128)) (Finset.mem_range.1 hc)]]
  rw [show (∑ c ∈ range 120, if wbit CrtGen.tables.g[c]! e then
      ((Array.range 120).map fun c => (⟨wordAt (Prover.senderColumns p iv key)[c]! p.labelRowOffset,
        wordAt (Prover.senderColumns p iv key)[c]! (p.labelRowOffset + 64)⟩ : W128))[c]!.toGF +
      (if dbit c then (⟨wordAt (proverU p iv key 0) p.labelRowOffset,
        wordAt (proverU p iv key 0) (p.labelRowOffset + 64)⟩ : W128).toGF else 0) else 0) =
      (∑ c ∈ range 120, if wbit CrtGen.tables.g[c]! e then
      ((Array.range 120).map fun c => (⟨wordAt (Prover.senderColumns p iv key)[c]! p.labelRowOffset,
        wordAt (Prover.senderColumns p iv key)[c]! (p.labelRowOffset + 64)⟩ : W128))[c]!.toGF
        else 0) + gf2 (∑ c ∈ range 120, zb (dbit c && wbit CrtGen.tables.g[c]! e)) *
      (⟨wordAt (proverU p iv key 0) p.labelRowOffset,
        wordAt (proverU p iv key 0) (p.labelRowOffset + 64)⟩ : W128).toGF by
    rw [map_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    cases wbit CrtGen.tables.g[c]! e <;> cases dbit c <;> simp]
  rw [← zb_wbit_gammaOf _ _ (by omega), CrtCheck.gf2_zb_mul]

lemma gateInputs_length (p : Params) (T : CrtTables) (iv : ByteArray) (cols : Array (Array UInt64)) :
    (gateInputs p T iv cols).length = 312 := by
  simp [gateInputs, Params.nMult]

lemma gateInputsOff_length' (p : Params) (T : CrtTables) (iv : ByteArray)
    (cols : Array (Array UInt64)) (off : W128) : (Prover.gateInputsOff p T iv cols off).length = 312 := by
  simp [Prover.gateInputsOff, Params.nMult]

/-- **The verifier's gate hashes** are the prover's `h^{γ_e}_e`. -/
theorem gateHashes_eq (h5 : ByteArray → ByteArray) (p : Params) (iv : ByteArray)
    (key : ℕ → ℕ → ByteArray) (dbit : ℕ → Bool) (hlab : p.labelRowOffset + 128 ≤ p.correctionRows)
    {e : ℕ} (he : e < 312) :
    (gateHashes h5 p CrtGen.tables iv (convertToVoleAt p dbit (proverCorr p iv key) iv key))[e]! =
      if wbit (gammaOf CrtGen.tables dbit) e then
        (gateWords ((Prover.gateInputsOff p CrtGen.tables iv (Prover.senderColumns p iv key)
          ⟨wordAt (proverU p iv key 0) p.labelRowOffset,
            wordAt (proverU p iv key 0) (p.labelRowOffset + 64)⟩).map h5))[e]!
      else (gateWords ((Prover.gateInputsOff p CrtGen.tables iv (Prover.senderColumns p iv key)
          W128.zero).map h5))[e]! := by
  have hq := gateInputs_eq p iv key dbit hlab he
  rw [gateHashes, ZK.Sim.gateWords_get _ (by simp [gateInputs_length, he])]
  simp only [List.getElem_map]
  split
  · rename_i hg
    rw [ZK.Sim.gateWords_get _ (by simp [gateInputsOff_length', he])]
    simp only [hg, ↓reduceIte] at hq
    simp only [List.getElem_map]
    congr 2
    exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans (hq.trans
      (List.getElem?_eq_getElem (by simp [gateInputsOff_length', he]))))
  · rename_i hg
    rw [ZK.Sim.gateWords_get _ (by simp [gateInputsOff_length', he])]
    simp only [hg, Bool.false_eq_true, ↓reduceIte] at hq
    simp only [List.getElem_map]
    congr 2
    exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans (hq.trans
      (List.getElem?_eq_getElem (by simp [gateInputsOff_length', he]))))

lemma u32_bit_any (x : UInt32) (m : ℕ) : ((x >>> m.toUInt32) &&& 1 == 1) = x.toNat.testBit (m % 32) := by
  have e : x >>> m.toUInt32 = x >>> (m % 32).toUInt32 := by
    apply UInt32.toNat_inj.1
    rw [UInt32.toNat_shiftRight, UInt32.toNat_shiftRight]
    congr 1
    simp [Nat.toUInt32]
  rw [e, ZK.Sim.u32_bit _ _ (Nat.mod_lt _ (by norm_num))]

lemma get!_extract (b : ByteArray) {s t k : ℕ} (hk : s + k < t) (ht : t ≤ b.size) :
    (b.extract s t).get! k = b.get! (s + k) := by
  rw [byteArray_get!_eq, byteArray_get!_eq, ByteArray.data_extract,
    Array.getElem?_extract]
  have : s + k < b.data.size := by have : b.size = b.data.size := rfl; omega
  have h' : k < min t b.data.size - s := by have : b.size = b.data.size := rfl; omega
  simp only [h', ↓reduceIte]

/-- **The verifier reads back the prover's `c_mult` bits.** -/
theorem cmult_bit (p : Params) (h0 h1 : Array UInt32) (uMask : Array W128) {m e : ℕ}
    (hm : m < p.nMask) (he : e < 312) :
    ((((Prover.fit (Prover.cMultOf p h0 h1 uMask) (p.nMask * p.nMultBytes)).extract
      (m * p.nMultBytes) ((m + 1) * p.nMultBytes)).get! (e / 8) >>> (e % 8).toUInt8) &&& 1 == 1) =
      ZK.Sim.cmultBit h0 h1 uMask m e := by
  have hsz : (Prover.cMultOf p h0 h1 uMask).size = p.nMask * p.nMultBytes := by
    rw [ZK.Sim.cMultOf_eq, ZK.Sim.size_ba]
  have h39 : p.nMultBytes = 39 := rfl
  have hlt : m * 39 + e / 8 < p.nMask * 39 := by
    have : (m + 1) * 39 ≤ p.nMask * 39 := Nat.mul_le_mul_right _ hm
    omega
  rw [fit_of_size hsz, get!_extract _ (by rw [h39]; omega) (by
      rw [hsz, h39]; exact Nat.mul_le_mul_right _ hm),
    ZK.Sim.cMultOf_eq, ZK.Sim.get!_ba _ (by rw [h39]; exact hlt)]
  simp only [ZK.Sim.cmultByte, h39]
  have e1 : (m * 39 + e / 8) / 39 = m := by omega
  have e2 : (m * 39 + e / 8) % 39 = e / 8 := by omega
  rw [e1, e2, u8_bit _ _ (Nat.mod_lt _ (by norm_num)),
    ZK.Sim.byteOf_testBit _ (Nat.mod_lt _ (by norm_num)), show 8 * (e / 8) + e % 8 = e by omega]

/-! ## The tree part of the masks -/

lemma regroup (k : ℕ) (A B : ℕ → ZMod 2) (P : ℕ → ℕ → ℕ → ZMod 2) (W : ℕ → GF128) :
    ∑ d ∈ range k, gf2 (∑ t ∈ range k, ∑ b ∈ range k, A b * B t * P b t d) * W d =
      ∑ b ∈ range k, gf2 (A b) * ∑ d ∈ range k, gf2 (∑ t ∈ range k, P b t d * B t) * W d := by
  simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun d _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ =>
    Finset.sum_congr rfl fun t _ => ?_
  ring

/-- The tree part of `L_c` (`CrtCheck.Lc`), with the mask's `u_low` bits `U t` of tree `i`. -/
noncomputable def treeL (c : ℕ) (U : ℕ → Bool) : GF128 :=
  ∑ d ∈ range (BAVC.kOf (BAVC.treeOf c)), gf2 (∑ t ∈ range (BAVC.kOf (BAVC.treeOf c)),
    zb ((CrtCheck.pmVal (BAVC.treeOf c) (c - BAVC.bitOffset (BAVC.treeOf c) + t)).testBit d) *
      zb (U t)) * CrtCheck.natGF (CrtCheck.wtL.getD (BAVC.bitOffset (BAVC.treeOf c) + d) 0)

lemma kOf_le (i : ℕ) : BAVC.kOf i ≤ 8 := by rw [kOf_eq]; split <;> omega

lemma maskRow_lt (p : Params) {m t : ℕ} (hm : m < p.nMask) (ht : t < 8) :
    p.correctionRows + 8 * m + t < 64 * (p.colBytes / 8) := by
  simp only [Params.colBytes, Params.voleColBlocks, Params.voleRows] at *
  omega

lemma sum_range_120' {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∑ c ∈ range 120, g c = ∑ i ∈ range BAVC.tau, ∑ b ∈ range (BAVC.kOf i), g (BAVC.bitOffset i + b) := by
  rw [sum_range_120, ← Fin.sum_univ_eq_sum_range (fun i => ∑ b ∈ range (BAVC.kOf i),
    g (BAVC.bitOffset i + b))]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Fin.sum_univ_eq_sum_range (fun b => g (BAVC.bitOffset i + b)) _

/-- **The tree part**: `W_tree · r̃(q)_m = W_tree · r̃(v)_m + Σ_c Δ_c · treeL_c(u^{(i)} on mask m)`. -/
theorem tree_part (p : Params) (iv : ByteArray) (key : ℕ → ℕ → ByteArray) (dbit : ℕ → Bool)
    {m : ℕ} (hm : m < p.nMask) :
    (W128.rowMul (rTildeOf CrtGen.tables ((Array.range 8).map fun t =>
      rowOf (convertToVoleAt p dbit (proverCorr p iv key) iv key)
        (p.correctionRows + 8 * m + t))).bit 120 CrtGen.tables.wTree).toGF =
    (W128.rowMul (rTildeOf CrtGen.tables ((Array.range 8).map fun t =>
      rowOf (Prover.senderColumns p iv key) (p.correctionRows + 8 * m + t))).bit 120
        CrtGen.tables.wTree).toGF +
    ∑ c ∈ range 120, gf2 (zb (dbit c)) * treeL c (fun t =>
      wbit (proverU p iv key (BAVC.treeOf c)) (p.correctionRows + 8 * m + t)) := by
  set U : ℕ → ℕ → Bool := fun i t => wbit (proverU p iv key i) (p.correctionRows + 8 * m + t)
  rw [rowMul_toGF, rowMul_toGF]
  -- Bit `j` of `r̃(q)`.
  have hbit : ∀ j < 120, zb ((rTildeOf CrtGen.tables ((Array.range 8).map fun t =>
      rowOf (convertToVoleAt p dbit (proverCorr p iv key) iv key)
        (p.correctionRows + 8 * m + t))).bit j) =
      zb ((rTildeOf CrtGen.tables ((Array.range 8).map fun t =>
        rowOf (Prover.senderColumns p iv key) (p.correctionRows + 8 * m + t))).bit j) +
      ∑ t ∈ range (BAVC.kOf (BAVC.treeOf j)), ∑ b ∈ range (BAVC.kOf (BAVC.treeOf j)),
        zb (dbit (BAVC.bitOffset (BAVC.treeOf j) + b)) * zb (U (BAVC.treeOf j) t) *
          zb ((polyMod ((1 : UInt64) <<< (b + t).toUInt64) CrtGen.tables.mI[BAVC.treeOf j]!).toNat.testBit
            (j - BAVC.bitOffset (BAVC.treeOf j))) := by
    intro j hj
    obtain ⟨hti, _, _⟩ := treeOf_spec hj
    rw [rTildeOf_bit _ _ hj, rTildeOf_bit _ _ hj, zb_polyMod_rTildeIn _ _ _ _ (kOf_le _),
      zb_polyMod_rTildeIn _ _ _ _ (kOf_le _), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b hb => ?_
    have ht := Finset.mem_range.1 ht
    have hb := Finset.mem_range.1 hb
    have ht8 : t < 8 := lt_of_lt_of_le ht (kOf_le _)
    rw [getElem!_range_map _ _ ht8, getElem!_range_map _ _ ht8,
      rowOf_bit _ _ (by have := pos_lt hti hb; omega), rowOf_bit _ _ (by have := pos_lt hti hb; omega),
      prover_column_mask p iv key dbit hti hb (by omega) (maskRow_lt p hm ht8), zb_xor, zb_and]
    ring
  rw [Finset.sum_congr rfl fun j hj => by
    rw [← CrtCheck.gf2_zb_mul, hbit j (Finset.mem_range.1 hj), map_add, add_mul],
    Finset.sum_add_distrib]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun j _ => CrtCheck.gf2_zb_mul _ _) ?_
  -- Regroup by tree.
  rw [sum_range_120', sum_range_120']
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi := Finset.mem_range.1 hi
  refine (Finset.sum_congr rfl fun d hd => ?_).trans ((regroup (BAVC.kOf i)
    (fun b => zb (dbit (BAVC.bitOffset i + b))) (fun t => zb (U i t))
    (fun b t d => zb ((polyMod ((1 : UInt64) <<< (b + t).toUInt64) CrtGen.tables.mI[i]!).toNat.testBit d))
    (fun d => CrtGen.tables.wTree[BAVC.bitOffset i + d]!.toGF)).trans
      (Finset.sum_congr rfl fun b hb => ?_))
  · rw [treeOf_pos (Finset.mem_range.1 hd), Nat.add_sub_cancel_left]
  have hb := Finset.mem_range.1 hb
  rw [treeL, treeOf_pos hb, Nat.add_sub_cancel_left]
  refine congrArg (gf2 (zb (dbit (BAVC.bitOffset i + b))) * ·) ?_
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd := Finset.mem_range.1 hd
  rw [wTree_toGF (pos_lt hi hd)]
  refine congrArg (fun x => gf2 x * _) ?_
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht := Finset.mem_range.1 ht
  rw [pmVal_eq hi (by have := kOf_le i; omega)]

/-! ## CRT completeness -/

/-- **The CRT identity on the prover's masks**: the tree and gate parts of `q_mask − v_mask` at `Δ`
are `u_mask · Δ'`. -/
theorem crt_core (p : Params) (iv : ByteArray) (key : ℕ → ℕ → ByteArray) (dbit : ℕ → Bool)
    (hi8 : UInt8) (m : ℕ) :
    let us : Array (Array UInt64) := (Array.range BAVC.tau).map fun i => proverU p iv key i
    let low : ℕ → Bool := fun c =>
      wbit us[BAVC.treeOf c]! (p.correctionRows + 8 * m + (c - BAVC.bitOffset (BAVC.treeOf c)))
    let a : W128 := (W128.rowMul low 120 CrtGen.tables.wCrt).xor
      (CrtGen.w128OfNat (CrtGen.pmul hi8.toNat Prover.mTree))
    (∑ c ∈ range 120, gf2 (zb (dbit c)) * treeL c (fun t =>
        wbit (proverU p iv key (BAVC.treeOf c)) (p.correctionRows + 8 * m + t))) +
      ∑ e ∈ range 312, gf2 (zb (wbit (gammaOf CrtGen.tables dbit) e && Prover.dot Prover.fRows[e]! a)) *
        CrtGen.tables.wGate[e]!.toGF =
      a.toGF * (W128.rowMul dbit 120 CrtGen.tables.wCrt).toGF := by
  intro us low a
  -- The mask's `u_low` bits and `⟨F[e], a⟩`, as linear forms of `a`.
  have hU : ∀ c < 120, ∀ t < BAVC.kOf (BAVC.treeOf c),
      zb (wbit (proverU p iv key (BAVC.treeOf c)) (p.correctionRows + 8 * m + t)) =
        formHom (ZK.maskInv.getD (BAVC.bitOffset (BAVC.treeOf c) + t) 0) a.toGF := by
    intro c hc t ht
    obtain ⟨hti, _, _⟩ := treeOf_spec hc
    rw [formHom_maskInv low hi8 (pos_lt hti ht)]
    simp only [low, us, treeOf_pos ht, Nat.add_sub_cancel_left]
    rw [getElem!_range_map _ _ hti]
  have hdot : ∀ e < 312, Prover.dot Prover.fRows[e]! a = form (CrtGen.F.toList.getD e 0) a.toGF :=
    fun e he => by rw [fRows_get he, dot_eq_form]
  -- Expand `γ` and regroup by `c`.
  have hgate : ∑ e ∈ range 312, gf2 (zb (wbit (gammaOf CrtGen.tables dbit) e &&
      Prover.dot Prover.fRows[e]! a)) * CrtGen.tables.wGate[e]!.toGF =
      ∑ c ∈ range 120, gf2 (zb (dbit c)) * ∑ e ∈ range 312,
        gf2 (zb ((CrtCheck.trRow CrtGen.G.toList c).testBit e) *
          formHom (CrtGen.F.toList.getD e 0) a.toGF) *
        CrtCheck.natGF (CrtCheck.trRow CrtGen.wGate.toList e) := by
    rw [Finset.sum_congr rfl fun e he => by
      rw [zb_and, zb_wbit_gammaOf _ _ (by have := Finset.mem_range.1 he; omega),
        hdot e (Finset.mem_range.1 he), wGate_toGF (Finset.mem_range.1 he)]]
    simp only [Finset.mul_sum, Finset.sum_mul, map_sum, map_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun e he => ?_
    rw [zb_and, map_mul, wbit_g_tables (Finset.mem_range.1 hc)
      (by have := Finset.mem_range.1 he; omega)]
    rw [show formHom (CrtGen.F.toList.getD e 0) a.toGF = zb (form (CrtGen.F.toList.getD e 0) a.toGF)
      from rfl]
    ring
  rw [hgate, ← Finset.sum_add_distrib, rowMul_toGF, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c hc => ?_
  have hc := Finset.mem_range.1 hc
  rw [← mul_add]
  have hL : treeL c (fun t => wbit (proverU p iv key (BAVC.treeOf c))
      (p.correctionRows + 8 * m + t)) + ∑ e ∈ range 312,
        gf2 (zb ((CrtCheck.trRow CrtGen.G.toList c).testBit e) *
          formHom (CrtGen.F.toList.getD e 0) a.toGF) *
        CrtCheck.natGF (CrtCheck.trRow CrtGen.wGate.toList e) = CrtCheck.Lc c a.toGF := by
    rw [CrtCheck.Lc, treeL]
    refine congrArg (· + _) (Finset.sum_congr rfl fun d _ => ?_)
    refine congrArg (fun x => gf2 x * _) (Finset.sum_congr rfl fun t ht => ?_)
    rw [hU c hc t (Finset.mem_range.1 ht)]
  rw [hL, CrtCheck.Lc_eq hc, ← liftCol_tables hc, liftCol, ← CrtCheck.gf2_zb_mul]
  ring

/-- **CRT completeness** (`crt_vole_commit` against `crt_vole_reconstruct`): for the generated
tables, every statement whose label rows are corrected rows (`labelRowOffset + 128 ≤ ℓ'`: the five
relations, either layout), and every `Δ`, the verifier's masks are `ṽ_mask + u_mask · Δ'`. -/
theorem crtComplete (Hs : Hashes) (p : Params) (mu1 wPrefix rho binder1 : ByteArray)
    (hlab : p.labelRowOffset + 128 ≤ p.correctionRows) :
    CrtComplete (Hs.hash .h5) CrtGen.tables
      (Prover.voleGen Hs CrtGen.tables p mu1 wPrefix rho binder1) := by
  intro dbit m hm
  set T := CrtGen.tables
  set s := Prover.voleGen Hs T p mu1 wPrefix rho binder1 with hs
  set key := leafKey s.leaves
  set iv := s.iv
  set vcols := Prover.senderColumns p iv key
  set qcols := convertToVoleAt p dbit (proverCorr p iv key) iv key
  set uPre : W128 := ⟨wordAt (proverU p iv key 0) p.labelRowOffset,
    wordAt (proverU p iv key 0) (p.labelRowOffset + 64)⟩
  set h0 := gateWords ((Prover.gateInputsOff p T iv vcols W128.zero).map (Hs.hash .h5))
  set h1 := gateWords ((Prover.gateInputsOff p T iv vcols uPre).map (Hs.hash .h5))
  set us : Array (Array UInt64) := (Array.range BAVC.tau).map fun i => proverU p iv key i
  have hp : s.params = p := rfl
  replace hm : m < p.nMask := hm
  have hvm : s.vMask = (crtReconstructWith h0 p (fun _ => false) ByteArray.empty T vcols).qMask :=
    rfl
  have hum : s.uMask = Prover.uMaskOf p T s.seed iv us := rfl
  have hcm : s.fields.cmult = Prover.cMultOf p h0 (gateWords ((Prover.gateInputsOff p T iv vcols
      ⟨wordAt s.u p.labelRowOffset, wordAt s.u (p.labelRowOffset + 64)⟩).map (Hs.hash .h5)))
      s.uMask := rfl
  have hu0 : s.u = proverU p iv key 0 := by
    show ((Array.range BAVC.tau).map fun i => Prover.smallVoleUWords p iv i (key i))[0]! = _
    rw [getElem!_range_map _ _ (by decide)]; rfl
  rw [hu0] at hcm
  simp only [hp]
  rw [hcm, hvm]
  set hi := AES.prg s.seed iv (((1 : UInt32) <<< 31) - 1) 0 ((8 * p.nMask + 127) / 128)
  have hmask : s.uMask[m]! = (W128.rowMul (fun c => wbit us[BAVC.treeOf c]!
      (p.correctionRows + 8 * m + (c - BAVC.bitOffset (BAVC.treeOf c)))) 120 T.wCrt).xor
      (CrtGen.w128OfNat (CrtGen.pmul (hi.get! m).toNat Prover.mTree)) := by
    rw [hum, Prover.uMaskOf, getElem!_range_map _ _ hm]
  -- Unfold both reconstructions at mask `m`.
  simp only [crtReconstructAt, crtReconstructWith]
  rw [getElem!_range_map _ _ hm, getElem!_range_map _ _ hm, getElem!_range_map _ _ hm,
    getElem!_range_map _ _ hm, toGF_xor, toGF_xor, tree_part p iv key dbit hm]
  -- The gate rows.
  have hrow : ∀ e < 312,
      (((gateHashes (Hs.hash .h5) p T iv qcols)[e]! >>> m.toUInt32) &&& 1 == 1 ^^
        (wbit (gammaOf T dbit) e && (((Prover.fit (Prover.cMultOf p h0 h1 s.uMask)
          (p.nMask * p.nMultBytes)).extract (m * p.nMultBytes) ((m + 1) * p.nMultBytes)).get!
            (e / 8) >>> (e % 8).toUInt8) &&& 1 == 1)) =
      ((((h0[e]! >>> m.toUInt32) &&& 1 == 1) ^^ (wbit (gammaOf T fun _ => false) e &&
        ((ByteArray.empty.extract (m * p.nMultBytes) ((m + 1) * p.nMultBytes)).get! (e / 8) >>>
          (e % 8).toUInt8) &&& 1 == 1)) ^^
        (wbit (gammaOf T dbit) e && Prover.dot Prover.fRows[e]! s.uMask[m]!)) := by
    intro e he
    rw [gateHashes_eq _ p iv key dbit hlab he, cmult_bit p h0 h1 s.uMask hm he, ZK.Sim.cmultBit,
      gammaOf_false T (by omega)]
    simp only [u32_bit_any, UInt32.toNat_xor, Nat.testBit_xor, Bool.false_and, Bool.xor_false]
    cases wbit (gammaOf T dbit) e <;> simp only [Bool.false_and, Bool.xor_false, Bool.true_and,
      Bool.false_eq_true, ↓reduceIte] <;>
      cases (h0[e]!).toNat.testBit (m % 32) <;> cases (h1[e]!).toNat.testBit (m % 32) <;>
      cases Prover.dot Prover.fRows[e]! s.uMask[m]! <;> rfl
  have hgate : (W128.rowMul (fun e =>
      ((gateHashes (Hs.hash .h5) p T iv qcols)[e]! >>> m.toUInt32) &&& 1 == 1 ^^
        (wbit (gammaOf T dbit) e && (((Prover.fit (Prover.cMultOf p h0 h1 s.uMask)
          (p.nMask * p.nMultBytes)).extract (m * p.nMultBytes) ((m + 1) * p.nMultBytes)).get!
            (e / 8) >>> (e % 8).toUInt8) &&& 1 == 1)) p.nMult T.wGate).toGF =
      (W128.rowMul (fun e => ((h0[e]! >>> m.toUInt32) &&& 1 == 1) ^^ (wbit (gammaOf T fun _ => false) e &&
        ((ByteArray.empty.extract (m * p.nMultBytes) ((m + 1) * p.nMultBytes)).get! (e / 8) >>>
          (e % 8).toUInt8) &&& 1 == 1)) p.nMult T.wGate).toGF +
      ∑ e ∈ range 312, gf2 (zb (wbit (gammaOf T dbit) e && Prover.dot Prover.fRows[e]! s.uMask[m]!)) *
        T.wGate[e]!.toGF := by
    rw [rowMul_toGF, rowMul_toGF, show p.nMult = 312 from rfl, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e he => ?_
    simp only [← CrtCheck.gf2_zb_mul]
    rw [hrow e (Finset.mem_range.1 he), zb_xor, map_add, add_mul]
  rw [hgate, hmask]
  have hcore := crt_core p iv key dbit (hi.get! m) m
  simp only at hcore
  rw [← hmask] at hcore ⊢
  rw [← hcore]
  ring

end VoleMole.Verifier.Bridge
