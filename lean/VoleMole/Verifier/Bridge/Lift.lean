import VoleMole.Arith.GFField
import VoleMole.Verifier.CrtGen
import VoleMole.Verifier.KOS
import VoleMole.SeedExtraction

/-!
# Bridge: the blocks of `Δ` and the CRT lift `W_CRT`

The extraction model (`SeedExtraction.lean`, `Claim4Hyp`) takes the challenge as blocks
`Δ' = (Δ_i)_{i < τ}`, `Δ_i ∈ F₂^{k_i}`, and an injective additive lift `e : Π_i B_i →+ F`. The
executable verifier works with the 16-byte `Δ`, its bits `c < 120` (`BAVC.deltaBit`), the hidden
indices `BAVC.hiddenIndex`, and `crt_lift_delta(Δ) = Σ_{c < 120} Δ_c · W_CRT[c]`
(`W128.rowMul dbit 120 T.wCrt`). This file fixes the model's side for the executable:

* `Blocks`: `B_i = Fin k_i → ZMod 2`; bit `b` of block `i` is bit `p_i + b` of `Δ`
  (`p_i = BAVC.bitOffset i = 0, 8, 15, …, 113`). `blocksOf dbit` reads the blocks off the bits and
  `dbitOf Δ'` writes them back (`dbitOf_blocksOf`, `blocksOf_dbitOf`); `sum_range_120` regroups a
  sum over the 120 bit positions by block.
* `lift T`: **the CRT lift** `Δ' ↦ Σ_{i, b} Δ_{i,b} · W_CRT[p_i + b]` as an additive map into
  `GF128` (a field, `Arith/GFField.lean`). `rowMul_lift`: the executable `crt_lift_delta` is
  `lift T (blocksOf dbit)`. `blockLift_lift`: the model's `e_i = e ∘ single i` is the lift of block
  `i` alone.
* `lift_injective`: **`W_CRT` is injective**, for any tables passing `liftInvOk`: an explicit left
  inverse `liftInv` (120 linear forms on `GF128`, computed offline by Gaussian elimination) with
  `⟨liftInv[c'], W_CRT[c]⟩ = [c = c']`. `liftInvOk_tables` checks this for `CrtGen.tables` in the
  kernel (`decide +kernel`, 120 · 120 parities of 128-bit words).

The linear forms are `⟨l, a⟩ = parity(l ∧ a)` on the two 64-bit words (`form`), `F₂`-linear by
`par_xor`.
-/

open Finset

namespace VoleMole.Verifier.Bridge

open VoleMole.Arith VoleMole.Verifier

noncomputable section

/-! ## Positions of the blocks -/

theorem kOf_eq (i : ℕ) : BAVC.kOf i = if i = 0 then 8 else 7 := by
  unfold BAVC.kOf; split_ifs <;> omega

theorem bitOffset_succ (i : ℕ) : BAVC.bitOffset (i + 1) = BAVC.bitOffset i + BAVC.kOf i := by
  simp [BAVC.bitOffset, List.range_succ, List.foldl_append]

/-- `p_i = 0` for `i = 0`, else `8 + 7 (i − 1)`. -/
theorem bitOffset_eq (i : ℕ) : BAVC.bitOffset i = if i = 0 then 0 else 7 * i + 1 := by
  induction i with
  | zero => simp [BAVC.bitOffset]
  | succ n ih => rw [bitOffset_succ, ih, kOf_eq]; split_ifs <;> omega

theorem pos_lt {i b : ℕ} (hi : i < BAVC.tau) (hb : b < BAVC.kOf i) :
    BAVC.bitOffset i + b < 120 := by
  simp only [BAVC.tau] at hi
  rw [bitOffset_eq]; rw [kOf_eq] at hb; split_ifs at * <;> omega

theorem pos_inj {i b i' b' : ℕ} (hb : b < BAVC.kOf i) (hb' : b' < BAVC.kOf i')
    (h : BAVC.bitOffset i + b = BAVC.bitOffset i' + b') : i = i' ∧ b = b' := by
  rw [bitOffset_eq, bitOffset_eq] at h; rw [kOf_eq] at hb hb'; split_ifs at * <;> omega

theorem treeOf_pos {i b : ℕ} (hb : b < BAVC.kOf i) : BAVC.treeOf (BAVC.bitOffset i + b) = i := by
  unfold BAVC.treeOf; rw [bitOffset_eq]; rw [kOf_eq] at hb
  by_cases hi : i = 0 <;> simp only [hi, ite_true, ite_false] at hb ⊢ <;> split_ifs <;> omega

theorem treeOf_spec {c : ℕ} (hc : c < 120) :
    BAVC.treeOf c < BAVC.tau ∧ BAVC.bitOffset (BAVC.treeOf c) ≤ c ∧
      c - BAVC.bitOffset (BAVC.treeOf c) < BAVC.kOf (BAVC.treeOf c) := by
  simp only [BAVC.tau]
  by_cases h8 : c < 8
  · simp [BAVC.treeOf, h8, bitOffset_eq, kOf_eq]
  · have : (c - 8) / 7 + 1 ≠ 0 := by omega
    simp only [BAVC.treeOf, h8, ite_false, bitOffset_eq, kOf_eq, this]; omega

/-- **Regrouping by block**: the 120 bit positions are the `p_i + b`, `i < τ`, `b < k_i`. -/
theorem sum_range_120 {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∑ c ∈ range 120, g c = ∑ i : Fin BAVC.tau, ∑ b : Fin (BAVC.kOf i), g (BAVC.bitOffset i + b) := by
  rw [Finset.sum_sigma']
  symm
  refine Finset.sum_bij (fun x _ => BAVC.bitOffset x.1 + x.2) (fun x _ =>
    mem_range.2 (pos_lt x.1.isLt x.2.isLt)) ?_ ?_ fun _ _ => rfl
  · rintro ⟨i, b⟩ _ ⟨i', b'⟩ _ h
    obtain ⟨h1, h2⟩ := pos_inj b.isLt b'.isLt h
    obtain rfl : i = i' := Fin.ext h1
    obtain rfl : b = b' := Fin.ext h2
    rfl
  · intro c hc
    obtain ⟨h1, h2, h3⟩ := treeOf_spec (mem_range.1 hc)
    exact ⟨⟨⟨_, h1⟩, ⟨_, h3⟩⟩, mem_sigma.2 ⟨mem_univ _, mem_univ _⟩, by simp only; omega⟩

/-! ## Blocks -/

/-- The challenge as blocks: `Δ_i ∈ F₂^{k_i}` for each small VOLE `i < τ`. -/
abbrev Blocks := ∀ i : Fin BAVC.tau, Fin (BAVC.kOf i) → ZMod 2

/-- A bit in `F₂`. -/
def zb (x : Bool) : ZMod 2 := if x then 1 else 0

@[simp] lemma zb_true : zb true = 1 := rfl
@[simp] lemma zb_false : zb false = 0 := rfl

lemma zb_xor (x y : Bool) : zb (x ^^ y) = zb x + zb y := by
  cases x <;> cases y <;> decide

lemma zb_and (x y : Bool) : zb (x && y) = zb x * zb y := by
  cases x <;> cases y <;> decide

/-- The blocks of the bits `dbit` of `Δ`: `Δ_{i,b} = dbit (p_i + b)`. -/
def blocksOf (dbit : ℕ → Bool) : Blocks := fun i b => zb (dbit (BAVC.bitOffset i + b))

/-- The bits of `Δ` from its blocks (`false` beyond the 120 block bits). -/
def dbitOf (Δ : Blocks) (c : ℕ) : Bool :=
  decide (∃ i : Fin BAVC.tau, ∃ b : Fin (BAVC.kOf i), BAVC.bitOffset i + b = c ∧ Δ i b = 1)

theorem dbitOf_blocksOf (dbit : ℕ → Bool) {c : ℕ} (hc : c < 120) :
    dbitOf (blocksOf dbit) c = dbit c := by
  obtain ⟨h1, h2, h3⟩ := treeOf_spec hc
  unfold dbitOf blocksOf
  by_cases hd : dbit c
  · simp only [hd, decide_eq_true_eq]
    refine ⟨⟨_, h1⟩, ⟨_, h3⟩, by simp only; omega, ?_⟩
    simp only [show BAVC.bitOffset (BAVC.treeOf c) + (c - BAVC.bitOffset (BAVC.treeOf c)) = c by
      omega, hd, zb_true]
  · simp only [hd, decide_eq_false_iff_not, not_exists, not_and]
    intro i b hib
    simp [hib, hd]

theorem dbitOf_ge (Δ : Blocks) {c : ℕ} (hc : 120 ≤ c) : dbitOf Δ c = false := by
  simp only [dbitOf, decide_eq_false_iff_not, not_exists, not_and]
  intro i b h
  have := pos_lt i.isLt b.isLt
  omega

theorem blocksOf_dbitOf (Δ : Blocks) : blocksOf (dbitOf Δ) = Δ := by
  funext i b
  simp only [blocksOf, dbitOf]
  by_cases h : Δ i b = 1
  · rw [h, decide_eq_true ⟨i, b, rfl, h⟩, zb_true]
  · have h0 : Δ i b = 0 := by
      generalize Δ i b = x at h ⊢; fin_cases x
      · rfl
      · exact absurd rfl h
    rw [h0, decide_eq_false, zb_false]
    rintro ⟨i', b', hib, h'⟩
    obtain ⟨h1, h2⟩ := pos_inj b'.isLt b.isLt hib
    obtain rfl : i' = i := Fin.ext h1
    obtain rfl : b' = b := Fin.ext h2
    exact h h'

/-! ## The lift -/

/-- Column `c` of `W_CRT` (the lift of the unit vector `e_c`), as a field element. -/
def liftCol (T : CrtTables) (c : ℕ) : GF128 := T.wCrt[c]!.toGF

/-- `F₂ ⊆ GF(2¹²⁸)`. -/
abbrev gf2 : ZMod 2 →+* GF128 := ZMod.castHom (dvd_refl 2) GF128

@[simp] lemma gf2_zb (x : Bool) : gf2 (zb x) = SeedExtraction.bit x := by
  cases x <;> simp [zb, SeedExtraction.bit]

/-- **The CRT lift** `Δ' ↦ Σ_{i, b} Δ_{i,b} · W_CRT[p_i + b]`. -/
def lift (T : CrtTables) : Blocks →+ GF128 where
  toFun Δ := ∑ i, ∑ b, gf2 (Δ i b) * liftCol T (BAVC.bitOffset i + b)
  map_zero' := by simp
  map_add' Δ Δ' := by simp [add_mul, Finset.sum_add_distrib]

theorem lift_apply (T : CrtTables) (Δ : Blocks) :
    lift T Δ = ∑ i, ∑ b, gf2 (Δ i b) * liftCol T (BAVC.bitOffset i + b) := rfl

/-- The model's `e_i = e ∘ single i` is the lift of block `i` alone. -/
theorem blockLift_lift (T : CrtTables) (i : Fin BAVC.tau) (x : Fin (BAVC.kOf i) → ZMod 2) :
    SeedExtraction.blockLift (lift T) i x = ∑ b, gf2 (x b) * liftCol T (BAVC.bitOffset i + b) := by
  simp only [SeedExtraction.blockLift, AddMonoidHom.comp_apply, AddMonoidHom.single_apply,
    lift_apply]
  rw [Finset.sum_eq_single i (fun i' _ hi' => by simp [Pi.single_eq_of_ne hi']) (by simp)]
  simp

/-- A `for` loop over `[0, n)` that always yields is a left fold over `List.range n`. -/
theorem forIn_range_foldl {β : Type} (n : ℕ) (init : β) (f : ℕ → β → Id (ForInStep β))
    (g : ℕ → β → β) (h : ∀ i b, f i b = pure (.yield (g i b))) :
    forIn [:n] init f = pure ((List.range n).foldl (fun b i => g i b) init) := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
  rw [show f = fun i b => pure (.yield (g i b)) from funext₂ h, List.forIn_pure_yield_eq_foldl]

lemma toGF_xor (a b : W128) : (a.xor b).toGF = a.toGF + b.toGF := rfl

lemma list_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ c ∈ range n, f c := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

/-- The executable row-times-matrix product over GF(2), in `GF128`. -/
theorem rowMul_toGF (x : ℕ → Bool) (n : ℕ) (M : Array W128) :
    (W128.rowMul x n M).toGF = ∑ c ∈ range n, if x c then M[c]!.toGF else 0 := by
  have h : ∀ (l : List ℕ) (a : W128),
      (l.foldl (fun acc i => if x i then acc.xor M[i]! else acc) a).toGF =
        a.toGF + (l.map fun c => if x c then M[c]!.toGF else 0).sum := by
    intro l
    induction l with
    | nil => simp
    | cons c l ih =>
      intro a
      rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]
      split_ifs <;> simp [toGF_xor, add_assoc]
  have h0 : W128.zero.toGF = 0 := rfl
  simp only [W128.rowMul, Id.run, bind_pure]
  rw [forIn_range_foldl _ _ _ (fun i acc => if x i then acc.xor M[i]! else acc)
    fun i b => by split_ifs <;> rfl]
  show W128.toGF (List.foldl _ _ _) = _
  rw [h, h0, zero_add, list_sum_range]

/-- **The executable `crt_lift_delta` is the lift of the blocks.** -/
theorem rowMul_lift (T : CrtTables) (dbit : ℕ → Bool) :
    (W128.rowMul dbit 120 T.wCrt).toGF = lift T (blocksOf dbit) := by
  rw [rowMul_toGF, sum_range_120]
  simp only [lift_apply, blocksOf, gf2_zb, liftCol]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => ?_
  cases dbit (BAVC.bitOffset i + b) <;> simp [SeedExtraction.bit]

/-! ## Injectivity of `W_CRT` -/

/-- One folding step of the parity computation. -/
def parStep (k x : ℕ) : ℕ := x ^^^ (x >>> k)

/-- The parity of the bits of `x < 2¹²⁸`. -/
def par (x : ℕ) : Bool :=
  (parStep 1 (parStep 2 (parStep 4 (parStep 8 (parStep 16 (parStep 32 (parStep 64 x))))))).testBit 0

lemma parStep_xor (k x y : ℕ) : parStep k (x ^^^ y) = parStep k x ^^^ parStep k y := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [parStep, Nat.testBit_xor, Nat.testBit_shiftRight]
  cases x.testBit i <;> cases y.testBit i <;> cases x.testBit (k + i) <;>
    cases y.testBit (k + i) <;> rfl

lemma par_xor (x y : ℕ) : par (x ^^^ y) = (par x ^^ par y) := by
  simp only [par, parStep_xor, Nat.testBit_xor]

lemma land_xor (l x y : ℕ) : l &&& (x ^^^ y) = (l &&& x) ^^^ (l &&& y) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_xor, Bool.and_xor_distrib_left]

/-- The `F₂`-linear form `a ↦ ⟨l, a⟩` on `GF128`, for a 128-bit mask `l`. -/
def form (l : ℕ) (a : GF128) : Bool :=
  par (l % 2 ^ 64 &&& a.lo.toNat) ^^ par (l / 2 ^ 64 &&& a.hi.toNat)

lemma form_add (l : ℕ) (a b : GF128) : form l (a + b) = (form l a ^^ form l b) := by
  show (par (_ &&& (a.lo ^^^ b.lo).toNat) ^^ par (_ &&& (a.hi ^^^ b.hi).toNat)) = _
  simp only [form, UInt64.toNat_xor, land_xor, par_xor]
  cases par (l % 2 ^ 64 &&& a.lo.toNat) <;> cases par (l % 2 ^ 64 &&& b.lo.toNat) <;>
    cases par (l / 2 ^ 64 &&& a.hi.toNat) <;> cases par (l / 2 ^ 64 &&& b.hi.toNat) <;> rfl

lemma form_zero (l : ℕ) : form l 0 = false := by
  show (par (_ &&& (0 : UInt64).toNat) ^^ par (_ &&& (0 : UInt64).toNat)) = false
  simp [par, parStep]

/-- `form l` as an additive map to `F₂`. -/
def formHom (l : ℕ) : GF128 →+ ZMod 2 where
  toFun a := zb (form l a)
  map_zero' := by simp [form_zero]
  map_add' a b := by simp [form_add, zb_xor]

lemma formHom_gf2_mul (l : ℕ) (x : ZMod 2) (a : GF128) : formHom l (gf2 x * a) = x * formHom l a := by
  rcases (by decide : ∀ y : ZMod 2, y = 0 ∨ y = 1) x with rfl | rfl <;> simp

/-- A left inverse of `W_CRT` (row `c'` is a 128-bit mask; computed offline). -/
def liftInv : List ℕ := [
  0x2c40719373d9a5880e326e7b34b101, 0x74c092b5946aee981256b28d5dd302, 0xe981256b28d5dd3024ad651abba604,
  0xff423b4522721fe84768a44e43fd08, 0xd2c40719373d9a5880e326e7b34b10, 0xa5880e326e7b34b101c64dcf669620,
  0x4b101c64dcf66962038c9b9ecd2c40, 0x962038c9b9ecd2c40719373d9a5880, 0xa99dd2c6f6b648e17cae689e286081,
  0xfaa6774b1bdad92385f2b9a278a182, 0xf54cee9637b5b2470be57344f14304, 0xea99dd2c6f6b648e17cae689e28608,
  0xd533ba58ded6c91c2f95cd13c50c10, 0xaa6774b1bdad92385f2b9a278a1820, 0x54cee9637b5b2470be57344f143040,
  0x4f70fe3b14bea85bce5660dae8c881, 0x9ee1fc76297d50b79cacc1b5d19102, 0x3dc3f8ec52faa16f3959836ba32204,
  0x34f70fe3b14bea85bce5660dae8c88, 0x69ee1fc76297d50b79cacc1b5d1910, 0xd3dc3f8ec52faa16f3959836ba3220,
  0xa7b87f1d8a5f542de72b306d746440, 0x8e75c260ab494f2350feede8b2f881, 0x929e46a1fddbd165f1033639d70982,
  0xab494f2350feede8b2f8819b1ceb84, 0xd8e75c260ab494f2350feede8b2f88, 0xb1ceb84c156929e46a1fddbd165f10,
  0x639d70982ad253c8d43fbb7a2cbe20, 0xc73ae13055a4a791a87f76f4597c40, 0x8bad833539ed0abe946e3f87796481,
  0x175b066a73da157d28dc7f0ef2c902, 0x2eb60cd4e7b42afa51b8fe1de59204, 0x5d6c19a9cf6855f4a371fc3bcb2408,
  0x3175b066a73da157d28dc7f0ef2c90, 0x62eb60cd4e7b42afa51b8fe1de5920, 0xc5d6c19a9cf6855f4a371fc3bcb240,
  0x74271a4bb73656bef0c4533d51fc81, 0xe84e34976e6cad7de188a67aa3f902, 0xa4bb73656bef0c4533d51fc8160e84,
  0x3d51fc8160e84e34976e6cad7de188, 0xe84e34976e6cad7de188a67aa3f90, 0x1d09c692edcd95afbc3114cf547f20,
  0x3a138d25db9b2b5f7862299ea8fe40, 0x5843a31394d2f5dc79922ad9fda81, 0xe8c4e534bd771e648ab67f6a06f82,
  0x189ca697aee3cc9156cfed40df0584, 0x31394d2f5dc79922ad9fda81be0b08, 0x62729a5ebb8f32455b3fb5037c1610,
  0xc1610e8c4e534bd771e648ab67f6a0, 0x82c21d189ca697aee3cc9156cfed40, 0xf3fa4aea9c6598bdc886b47826c281,
  0x140edf3fa4aea9c6598bdc886b4782, 0x281dbe7f495d538cb317b910d68f04, 0xa3c136140edf3fa4aea9c6598bdc88,
  0x47826c281dbe7f495d538cb317b910, 0x7cfe92baa719662f7221ad1e09b0a0, 0xf9fd25754e32cc5ee4435a3c136140,
  0xc55e651187beb53676e92c72170681, 0x8abcca230f7d6a6cedd258e42e0d02, 0x157994461efad4d9dba4b1c85c1a04,
  0xefad4d9dba4b1c85c1a04fe2af3288, 0x1a04fe2af3288c3df5a9b3b7496390, 0xf157994461efad4d9dba4b1c85c1a0,
  0xe2af3288c3df5a9b3b7496390b8340, 0x4fef8ea95e99cd622ec8796e0a3681, 0xd03093fbe3aa57a673588bb21e5b82,
  0xef8ea95e99cd622ec8796e0a368184, 0x90f2dc146d03093fbe3aa57a673588, 0x6e0a3681849fdf1d52bd339ac45d90,
  0x93fbe3aa57a673588bb21e5b828da0, 0x27f7c754af4ce6b117643cb7051b40, 0xa3c8b3a9f438936b7b1a5dccabf81,
  0x147916753e87126d6f634bb9957f02, 0x28f22cea7d0e24dadec697732afe04, 0x51e459d4fa1c49b5bd8d2ee655fc08,
  0xa3c8b3a9f438936b7b1a5dccabf810, 0x47916753e87126d6f634bb9957f020, 0x851e459d4fa1c49b5bd8d2ee655fc0,
  0x2e3ddafe986852d956209f39233781, 0x72466f03a8b8f76bfa61a14b655882, 0xe48cde075171eed7f4c34296cab104,
  0xe72466f03a8b8f76bfa61a14b65588, 0xce48cde075171eed7f4c34296cab10, 0x9c919bc0ea2e3ddafe986852d95620,
  0x171eed7f4c34296cab104f9c919bc0, 0x624e7c82354da50b0cbfadde3a2b81, 0xa6d285865fd6ef1d15c0f6624e7c82,
  0x4da50b0cbfadde3a2b81ecc49cf904, 0x9b4a16197f5bbc745703d98939f208, 0x54da50b0cbfadde3a2b81ecc49cf90,
  0xa9b4a16197f5bbc745703d98939f20, 0x31273e411aa6d285865fd6ef1d15c0, 0xb20f16b089de8cd31caba92fe7db81,
  0x641e2d6113bd19a63957525fcfb702, 0x7a334c72aea4bf9f6e050d9078b584, 0xf46698e55d497f3edc0a1b20f16b08,
  0x5ac2277a334c72aea4bf9f6e050d90, 0xb5844ef46698e55d497f3edc0a1b20, 0xd9078b5844ef46698e55d497f3edc0,
  0xfcdaa24cf1dd7a594e462e10d07d81, 0xf9b54499e3baf4b29c8c5c21a0fb02, 0xfb02b7f36a8933c775e9653918b84,
  0x1f6056fe6d512678eebd2ca7231708, 0x3ec0adfcdaa24cf1dd7a594e462e10, 0x815bf9b54499e3baf4b29c8c5c21a0,
  0xfe6d512678eebd2ca7231708683ec0, 0x387c5b31a6fee7a0af244276a97581, 0x4884ed52eb0328e1f16cc69bfb9e82,
  0xa975819470f8b6634dfdcf415e4884, 0x6a975819470f8b6634dfdcf415e488, 0xd52eb0328e1f16cc69bfb9e82bc910,
  0x92213b54bac0ca387c5b31a6fee7a0, 0x1c3e2d98d37f73d05792213b54bac0, 0xa68bdbbf856279496a8321d738d981,
  0x4d17b77f0ac4f292d50643ae71b302, 0x9a2f6efe1589e525aa0c875ce36604, 0x345eddfc2b13ca4b54190eb9c6cc08,
  0xce366047d345eddfc2b13ca4b54190, 0x3ae71b3023e9a2f6efe1589e525aa0, 0xd345eddfc2b13ca4b54190eb9c6cc0]

/-- `⟨liftInv[c'], W_CRT[c]⟩ = [c = c']` for all `c, c' < 120`. -/
def liftInvOk (T : CrtTables) : Bool :=
  (List.range 120).all fun c' =>
    let l := liftInv.getD c' 0
    (List.range 120).all fun c => form l (liftCol T c) == (c == c')

/-- The certificate holds for faest-arch-opt's tables (kernel computation). -/
theorem liftInvOk_tables : liftInvOk CrtGen.tables = true := by decide +kernel

theorem form_liftCol {T : CrtTables} (hT : liftInvOk T = true) {c c' : ℕ} (hc : c < 120)
    (hc' : c' < 120) : form (liftInv.getD c' 0) (liftCol T c) = (c == c') := by
  simp only [liftInvOk, List.all_eq_true, List.mem_range, beq_iff_eq] at hT
  exact hT c' hc' c hc

/-- **`W_CRT` is injective**, so the model's `Claim4Hyp.lift_inj` holds for the executable lift. -/
theorem lift_injective {T : CrtTables} (hT : liftInvOk T = true) : Function.Injective (lift T) := by
  refine (injective_iff_map_eq_zero (lift T)).2 fun Δ h => ?_
  funext i b
  have key := congrArg (formHom (liftInv.getD (BAVC.bitOffset i + b) 0)) h
  simp only [lift_apply, map_sum, formHom_gf2_mul, map_zero] at key
  have hf : ∀ (i' : Fin BAVC.tau) (b' : Fin (BAVC.kOf i')),
      formHom (liftInv.getD (BAVC.bitOffset i + b) 0) (liftCol T (BAVC.bitOffset i' + b')) =
        if BAVC.bitOffset i' + (b' : ℕ) = BAVC.bitOffset i + b then 1 else 0 := by
    intro i' b'
    show zb _ = _
    rw [form_liftCol hT (pos_lt i'.isLt b'.isLt) (pos_lt i.isLt b.isLt)]
    by_cases hh : BAVC.bitOffset i' + (b' : ℕ) = BAVC.bitOffset i + b <;>
      simp [hh, beq_eq_false_iff_ne.2]
  have key2 : ∑ i' : Fin BAVC.tau, ∑ b' : Fin (BAVC.kOf i'), Δ i' b' *
      (if BAVC.bitOffset i' + (b' : ℕ) = BAVC.bitOffset i + b then 1 else 0) = 0 := by
    exact (Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun b' _ => by rw [hf]).trans key
  rw [Finset.sum_eq_single i, Finset.sum_eq_single b] at key2
  · simpa using key2
  · intro b' _ hb'
    have : BAVC.bitOffset i + (b' : ℕ) ≠ BAVC.bitOffset i + b := fun hh => hb' (Fin.ext (by omega))
    simp only [this, ↓reduceIte, mul_zero]
  · simp
  · intro i' _ hi'
    refine Finset.sum_eq_zero fun b' _ => ?_
    have : BAVC.bitOffset i' + (b' : ℕ) ≠ BAVC.bitOffset i + b := fun hh =>
      hi' (Fin.ext (pos_inj b'.isLt b.isLt hh).1)
    simp only [this, ↓reduceIte, mul_zero]
  · simp

end

end VoleMole.Verifier.Bridge
