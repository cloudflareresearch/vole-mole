import VoleMole.Verifier.Bridge.Lift
import VoleMole.ZK.Push
import VoleMole.Verifier.Prover

/-!
# The CRT mask assembly is a bijection (`lean/docs/zk.md` §7.4, "Assembly")

`u_mask[m] = W_CRT · u_low[m] ⊕ M_tree · u_hi[m]` (`compute_u_mask`, `Sim.uMaskOfHi`): `u_low[m]`
takes `k_i` bits from byte `VOLE_CORRECTION_BYTES + m` of each small VOLE's input `u^{(i)}` (120
bits in all) and `u_hi[m]` is a byte of the root PRG's output. The 120 rows of `W_CRT` and the 8
polynomials `M_tree · X^j` (`deg M_tree = 120`) are a basis of `GF(2)¹²⁸`, so the assembly is a
bijection from the 128 used bits onto `GF128`, and uniform pads give a uniform mask.

* `byteBits`, `byteBitsEquiv`: a byte as its 8 bits (`byteBits_xor`: XOR is addition).
* `pmul_xor`, `pmul_byte`: the carry-less product is additive in its first argument, so
  `M_tree · u_hi = Σ_j u_hi,j · pmul(2^j, M_tree)`.
* `maskInv`, `maskInvOk_tables`: an explicit left inverse of the 128 columns (128 linear forms,
  computed offline by Gaussian elimination), checked in the kernel (`decide +kernel`).
* `crtVal`: one mask from its pads (`(Fin 17 → UInt8) × UInt8`), exactly as `uMaskOfHi` computes
  it. **`balanced_crtVal`**: it is balanced, so a uniform `(u_low, u_hi)` gives a uniform
  `u_mask[m]` (the 16 bits `7` of the 7-bit trees are unused).
-/

open Finset

namespace VoleMole.ZK

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith

noncomputable section

/-! ## Bytes as bits -/

/-- The 8 bits of a byte. -/
def byteBits (x : UInt8) : Fin 8 → Bool := fun j => x.toNat.testBit j

lemma byteBits_injective : Function.Injective byteBits := by
  intro x y h
  apply UInt8.toNat_inj.1
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 8
  · exact congrFun h ⟨i, hi⟩
  · have hx : x.toNat < 2 ^ i :=
      lt_of_lt_of_le x.toNat_lt (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hy : y.toNat < 2 ^ i :=
      lt_of_lt_of_le y.toNat_lt (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_eq_false_of_lt hx, Nat.testBit_eq_false_of_lt hy]

lemma card_uint8' : Fintype.card UInt8 = 2 ^ 8 := by
  rw [← FinEnum.card_eq_fintypeCard]; rfl

/-- A byte is its 8 bits. -/
def byteBitsEquiv : UInt8 ≃ (Fin 8 → Bool) :=
  Equiv.ofBijective byteBits ((Fintype.bijective_iff_injective_and_card _).2
    ⟨byteBits_injective, by rw [card_uint8', Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin]⟩)

@[simp] lemma byteBitsEquiv_apply (x : UInt8) : byteBitsEquiv x = byteBits x := rfl

lemma byteBits_xor (x y : UInt8) : byteBits (x ^^^ y) = byteBits x + byteBits y := by
  funext j
  simp [byteBits, UInt8.toNat_xor, Nat.testBit_xor, Bool.add_eq_xor]

/-! ## The carry-less product, linearly -/

lemma pmul_eq_foldl (a b : ℕ) : CrtGen.pmul a b =
    (List.range (b.log2 + 1)).foldl (fun r i => if b.testBit i then r ^^^ (a <<< i) else r) 0 := by
  simp only [CrtGen.pmul, Id.run, bind_pure]
  rw [forIn_range_foldl _ _ _ (fun i r => if b.testBit i then r ^^^ (a <<< i) else r)
    fun i r => by split_ifs <;> rfl]
  rfl

lemma shiftLeft_xor' (a a' i : ℕ) : (a ^^^ a') <<< i = (a <<< i) ^^^ (a' <<< i) := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_shiftLeft, Nat.testBit_xor]
  by_cases h : i ≤ k <;> simp [h]

lemma foldl_pmul_xor (a a' b : ℕ) : ∀ (l : List ℕ) (r r' : ℕ),
    l.foldl (fun r i => if b.testBit i then r ^^^ ((a ^^^ a') <<< i) else r) (r ^^^ r') =
      l.foldl (fun r i => if b.testBit i then r ^^^ (a <<< i) else r) r ^^^
        l.foldl (fun r i => if b.testBit i then r ^^^ (a' <<< i) else r) r'
  | [], _, _ => rfl
  | i :: l, r, r' => by
    simp only [List.foldl_cons]
    split_ifs
    · rw [shiftLeft_xor', show r ^^^ r' ^^^ ((a <<< i) ^^^ (a' <<< i)) =
        (r ^^^ (a <<< i)) ^^^ (r' ^^^ (a' <<< i)) by ac_rfl]
      exact foldl_pmul_xor a a' b l _ _
    · exact foldl_pmul_xor a a' b l _ _

/-- The carry-less product is additive in its first argument. -/
lemma pmul_xor (a a' b : ℕ) : CrtGen.pmul (a ^^^ a') b = CrtGen.pmul a b ^^^ CrtGen.pmul a' b := by
  rw [pmul_eq_foldl, pmul_eq_foldl, pmul_eq_foldl, ← foldl_pmul_xor a a' b _ 0 0]
  rfl

lemma pmul_zero_left (b : ℕ) : CrtGen.pmul 0 b = 0 := by
  rw [pmul_eq_foldl]
  simp only [Nat.zero_shiftLeft, Nat.xor_zero, ite_self]
  induction (List.range (b.log2 + 1)) with
  | nil => rfl
  | cons i l ih => simp [ih]

/-- A byte as the XOR of its bits. -/
lemma byte_eq_xor (h : UInt8) : h.toNat =
    (List.range 8).foldl (fun acc j => acc ^^^ (if h.toNat.testBit j then 2 ^ j else 0)) 0 := by
  have key : ∀ (n : ℕ) (acc : ℕ),
      ((List.range n).foldl (fun acc j => acc ^^^ (if h.toNat.testBit j then 2 ^ j else 0)) acc) =
        acc ^^^ (h.toNat % 2 ^ n) := by
    intro n
    induction n with
    | zero => intro acc; simp only [List.range_zero, List.foldl_nil, pow_zero, Nat.mod_one,
        Nat.xor_zero]
    | succ n ih =>
      intro acc
      rw [List.range_succ, List.foldl_append, ih]
      simp only [List.foldl_cons, List.foldl_nil, Nat.xor_assoc]
      congr 1
      apply Nat.eq_of_testBit_eq
      intro k
      simp only [Nat.testBit_xor, Nat.testBit_mod_two_pow]
      split_ifs with hb
      · rw [Nat.testBit_two_pow]
        by_cases hk : k < n
        · simp [hk, show k < n + 1 by omega, show n ≠ k by omega]
        · by_cases hkn : k = n
          · subst hkn; simp [hb]
          · simp [show ¬ k < n + 1 by omega, hk, show n ≠ k by omega]
      · simp only [Nat.zero_testBit, Bool.xor_false]
        by_cases hk : k < n
        · simp [hk, show k < n + 1 by omega]
        · by_cases hkn : k = n
          · subst hkn; simp [hb]
          · simp [show ¬ k < n + 1 by omega, hk]
  rw [key, Nat.zero_xor, Nat.mod_eq_of_lt (by simpa using h.toNat_lt)]

lemma pmul_foldl_xor (b : ℕ) (f : ℕ → ℕ) : ∀ (l : List ℕ) (acc : ℕ),
    CrtGen.pmul (l.foldl (fun acc j => acc ^^^ f j) acc) b =
      l.foldl (fun acc j => acc ^^^ CrtGen.pmul (f j) b) (CrtGen.pmul acc b)
  | [], _ => rfl
  | j :: l, acc => by
    simp only [List.foldl_cons]
    rw [pmul_foldl_xor b f l, pmul_xor]

/-- `M_tree · u_hi = Σ_j u_hi,j · pmul(2^j, M_tree)`. -/
lemma pmul_byte (h : UInt8) (b : ℕ) : CrtGen.pmul h.toNat b =
    (List.range 8).foldl (fun acc j => acc ^^^ (if h.toNat.testBit j then CrtGen.pmul (2 ^ j) b
      else 0)) 0 := by
  conv_lhs => rw [byte_eq_xor h]
  rw [pmul_foldl_xor, pmul_zero_left]
  congr 1
  funext acc j
  split_ifs <;> simp [pmul_zero_left]

/-! ## The mask from its pads -/

lemma w128OfNat_xor (x y : ℕ) :
    CrtGen.w128OfNat (x ^^^ y) = (CrtGen.w128OfNat x).xor (CrtGen.w128OfNat y) := by
  have hmod : ∀ a b : ℕ, (a ^^^ b) % 2 ^ 64 = a % 2 ^ 64 ^^^ b % 2 ^ 64 := fun a b => by
    apply Nat.eq_of_testBit_eq; intro k
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor]
    by_cases hk : k < 64 <;> simp [hk]
  have hdiv : ∀ a b : ℕ, (a ^^^ b) / 2 ^ 64 = a / 2 ^ 64 ^^^ b / 2 ^ 64 := fun a b => by
    apply Nat.eq_of_testBit_eq; intro k
    simp only [Nat.testBit_div_two_pow, Nat.testBit_xor]
  have hu : ∀ a b : ℕ, a < 2 ^ 64 → b < 2 ^ 64 → (a ^^^ b).toUInt64 = a.toUInt64 ^^^ b.toUInt64 :=
    fun a b ha hb => by
      apply UInt64.toNat_inj.1
      have e : ∀ n : ℕ, n.toUInt64.toNat = n % 2 ^ 64 := fun n => by simp
      rw [UInt64.toNat_xor, e, e, e, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
        Nat.mod_eq_of_lt (Nat.xor_lt_two_pow ha hb)]
  simp only [CrtGen.w128OfNat, W128.xor, hmod, hdiv]
  rw [hu _ _ (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)),
    hu _ _ (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))]

/-- The `u_low` bits of one mask, from the 17 pad bytes (bit `c − p_i` of tree `i`'s byte). -/
def crtLow (l : Fin BAVC.tau → UInt8) (c : ℕ) : Bool :=
  if h : BAVC.treeOf c < BAVC.tau then (l ⟨BAVC.treeOf c, h⟩).toNat.testBit
    (c - BAVC.bitOffset (BAVC.treeOf c)) else false

/-- One mask `u_mask[m]` from its pads, as `uMaskOfHi` computes it. -/
def crtW (T : CrtTables) (l : Fin BAVC.tau → UInt8) (h : UInt8) : W128 :=
  (W128.rowMul (crtLow l) 120 T.wCrt).xor (CrtGen.w128OfNat (CrtGen.pmul h.toNat Prover.mTree))

/-- `u_mask[m]` as a field element. -/
def crtVal (T : CrtTables) (l : Fin BAVC.tau → UInt8) (h : UInt8) : GF128 := (crtW T l h).toGF

/-- The 128 columns of the assembly: `W_CRT[c]` and `pmul(2^j, M_tree)`. -/
def maskCol (T : CrtTables) (k : ℕ) : GF128 :=
  if k < 120 then T.wCrt[k]!.toGF
  else (CrtGen.w128OfNat (CrtGen.pmul (2 ^ (k - 120)) Prover.mTree)).toGF

lemma toGF_w128OfNat_foldl (f : ℕ → ℕ) : ∀ (l : List ℕ) (acc : ℕ),
    (CrtGen.w128OfNat (l.foldl (fun acc j => acc ^^^ f j) acc)).toGF =
      (CrtGen.w128OfNat acc).toGF + (l.map fun j => (CrtGen.w128OfNat (f j)).toGF).sum
  | [], _ => by simp
  | j :: l, acc => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [toGF_w128OfNat_foldl f l, w128OfNat_xor, toGF_xor, add_assoc]

lemma w128OfNat_zero_toGF : (CrtGen.w128OfNat 0).toGF = 0 := rfl

/-- `crtVal` as a sum of columns. -/
theorem crtVal_eq (T : CrtTables) (l : Fin BAVC.tau → UInt8) (h : UInt8) :
    crtVal T l h = ∑ c ∈ range 120, (if crtLow l c then maskCol T c else 0) +
      ∑ j : Fin 8, (if byteBits h j then maskCol T (120 + j) else 0) := by
  rw [crtVal, crtW, toGF_xor, rowMul_toGF, pmul_byte, toGF_w128OfNat_foldl, w128OfNat_zero_toGF, zero_add]
  congr 1
  rw [list_sum_range (M := GF128), ← Fin.sum_univ_eq_sum_range (α := GF128)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [maskCol, show ¬ 120 + (j : ℕ) < 120 by omega, ↓reduceIte, Nat.add_sub_cancel_left,
    byteBits]
  split_ifs <;> rfl

/-! ## The certificate -/

/-- A left inverse of the 128 columns (row `k` is a 128-bit mask; computed offline). -/
def maskInv : List ℕ := [
  0xcd2c40719373d9a5880e326e7b34b101, 0x5774c092b5946aee981256b28d5dd302,
  0xaee981256b28d5dd3024ad651abba604, 0x90ff423b4522721fe84768a44e43fd08,
  0xecd2c40719373d9a5880e326e7b34b10, 0xd9a5880e326e7b34b101c64dcf669620,
  0xb34b101c64dcf66962038c9b9ecd2c40, 0x66962038c9b9ecd2c40719373d9a5880,
  0xfea99dd2c6f6b648e17cae689e286081, 0x3faa6774b1bdad92385f2b9a278a182,
  0x7f54cee9637b5b2470be57344f14304, 0xfea99dd2c6f6b648e17cae689e28608,
  0x1fd533ba58ded6c91c2f95cd13c50c10, 0x3faa6774b1bdad92385f2b9a278a1820,
  0x7f54cee9637b5b2470be57344f143040, 0x934f70fe3b14bea85bce5660dae8c881,
  0x269ee1fc76297d50b79cacc1b5d19102, 0x4d3dc3f8ec52faa16f3959836ba32204,
  0x934f70fe3b14bea85bce5660dae8c88, 0x1269ee1fc76297d50b79cacc1b5d1910,
  0x24d3dc3f8ec52faa16f3959836ba3220, 0x49a7b87f1d8a5f542de72b306d746440,
  0xcd8e75c260ab494f2350feede8b2f881, 0x56929e46a1fddbd165f1033639d70982,
  0x60ab494f2350feede8b2f8819b1ceb84, 0xcd8e75c260ab494f2350feede8b2f88,
  0x19b1ceb84c156929e46a1fddbd165f10, 0x33639d70982ad253c8d43fbb7a2cbe20,
  0x66c73ae13055a4a791a87f76f4597c40, 0x898bad833539ed0abe946e3f87796481,
  0x13175b066a73da157d28dc7f0ef2c902, 0x262eb60cd4e7b42afa51b8fe1de59204,
  0x4c5d6c19a9cf6855f4a371fc3bcb2408, 0x113175b066a73da157d28dc7f0ef2c90,
  0x2262eb60cd4e7b42afa51b8fe1de5920, 0x44c5d6c19a9cf6855f4a371fc3bcb240,
  0xb074271a4bb73656bef0c4533d51fc81, 0x60e84e34976e6cad7de188a67aa3f902,
  0x71a4bb73656bef0c4533d51fc8160e84, 0x533d51fc8160e84e34976e6cad7de188,
  0x160e84e34976e6cad7de188a67aa3f90, 0x2c1d09c692edcd95afbc3114cf547f20,
  0x583a138d25db9b2b5f7862299ea8fe40, 0xdf05843a31394d2f5dc79922ad9fda81,
  0x610e8c4e534bd771e648ab67f6a06f82, 0x1d189ca697aee3cc9156cfed40df0584,
  0x3a31394d2f5dc79922ad9fda81be0b08, 0x7462729a5ebb8f32455b3fb5037c1610,
  0x37c1610e8c4e534bd771e648ab67f6a0, 0x6f82c21d189ca697aee3cc9156cfed40,
  0xedf3fa4aea9c6598bdc886b47826c281, 0x36140edf3fa4aea9c6598bdc886b4782,
  0x6c281dbe7f495d538cb317b910d68f04, 0x35a3c136140edf3fa4aea9c6598bdc88,
  0x6b47826c281dbe7f495d538cb317b910, 0x3b7cfe92baa719662f7221ad1e09b0a0,
  0x76f9fd25754e32cc5ee4435a3c136140, 0x9fc55e651187beb53676e92c72170681,
  0x3f8abcca230f7d6a6cedd258e42e0d02, 0x7f157994461efad4d9dba4b1c85c1a04,
  0x61efad4d9dba4b1c85c1a04fe2af3288, 0x5c1a04fe2af3288c3df5a9b3b7496390,
  0x27f157994461efad4d9dba4b1c85c1a0, 0x4fe2af3288c3df5a9b3b7496390b8340,
  0xc24fef8ea95e99cd622ec8796e0a3681, 0x46d03093fbe3aa57a673588bb21e5b82,
  0x4fef8ea95e99cd622ec8796e0a368184, 0x5d90f2dc146d03093fbe3aa57a673588,
  0x796e0a3681849fdf1d52bd339ac45d90, 0x3093fbe3aa57a673588bb21e5b828da0,
  0x6127f7c754af4ce6b117643cb7051b40, 0x830a3c8b3a9f438936b7b1a5dccabf81,
  0x6147916753e87126d6f634bb9957f02, 0xc28f22cea7d0e24dadec697732afe04,
  0x1851e459d4fa1c49b5bd8d2ee655fc08, 0x30a3c8b3a9f438936b7b1a5dccabf810,
  0x6147916753e87126d6f634bb9957f020, 0x41851e459d4fa1c49b5bd8d2ee655fc0,
  0xea2e3ddafe986852d956209f39233781, 0x3e72466f03a8b8f76bfa61a14b655882,
  0x7ce48cde075171eed7f4c34296cab104, 0x13e72466f03a8b8f76bfa61a14b65588,
  0x27ce48cde075171eed7f4c34296cab10, 0x4f9c919bc0ea2e3ddafe986852d95620,
  0x75171eed7f4c34296cab104f9c919bc0, 0xf6624e7c82354da50b0cbfadde3a2b81,
  0x1aa6d285865fd6ef1d15c0f6624e7c82, 0x354da50b0cbfadde3a2b81ecc49cf904,
  0x6a9b4a16197f5bbc745703d98939f208, 0x2354da50b0cbfadde3a2b81ecc49cf90,
  0x46a9b4a16197f5bbc745703d98939f20, 0x7b31273e411aa6d285865fd6ef1d15c0,
  0xa1b20f16b089de8cd31caba92fe7db81, 0x43641e2d6113bd19a63957525fcfb702,
  0x277a334c72aea4bf9f6e050d9078b584, 0x4ef46698e55d497f3edc0a1b20f16b08,
  0x3c5ac2277a334c72aea4bf9f6e050d90, 0x78b5844ef46698e55d497f3edc0a1b20,
  0x50d9078b5844ef46698e55d497f3edc0, 0xadfcdaa24cf1dd7a594e462e10d07d81,
  0x5bf9b54499e3baf4b29c8c5c21a0fb02, 0x1a0fb02b7f36a8933c775e9653918b84,
  0x341f6056fe6d512678eebd2ca7231708, 0x683ec0adfcdaa24cf1dd7a594e462e10,
  0x7d815bf9b54499e3baf4b29c8c5c21a0, 0x56fe6d512678eebd2ca7231708683ec0,
  0xca387c5b31a6fee7a0af244276a97581, 0x5e4884ed52eb0328e1f16cc69bfb9e82,
  0x76a975819470f8b6634dfdcf415e4884, 0x276a975819470f8b6634dfdcf415e488,
  0x4ed52eb0328e1f16cc69bfb9e82bc910, 0x5792213b54bac0ca387c5b31a6fee7a0,
  0x651c3e2d98d37f73d05792213b54bac0, 0x8fa68bdbbf856279496a8321d738d981,
  0x1f4d17b77f0ac4f292d50643ae71b302, 0x3e9a2f6efe1589e525aa0c875ce36604,
  0x7d345eddfc2b13ca4b54190eb9c6cc08, 0x75ce366047d345eddfc2b13ca4b54190,
  0x643ae71b3023e9a2f6efe1589e525aa0, 0x47d345eddfc2b13ca4b54190eb9c6cc0,
  0x3f000000000000000000000000000000, 0x7e000000000000000000000000000000,
  0xfc000000000000000000000000000000, 0xf8000000000000000000000000000000,
  0xf0000000000000000000000000000000, 0xe0000000000000000000000000000000,
  0xc0000000000000000000000000000000, 0x80000000000000000000000000000000]

/-- `⟨maskInv[k], col_c⟩ = [c = k]` for all `c, k < 128`. -/
def maskInvOk (T : CrtTables) : Bool :=
  (List.range 128).all fun k =>
    let l := maskInv.getD k 0
    (List.range 128).all fun c => form l (maskCol T c) == (c == k)

/-- Pick the bit of tree `treeOf c` at position `c − p_i` (the bits of `u_low` in `crtLin`). -/
def selLow (x : Fin BAVC.tau → Fin 8 → Bool) (c : ℕ) : Bool :=
  if h : BAVC.treeOf c < BAVC.tau then
    (if h' : c - BAVC.bitOffset (BAVC.treeOf c) < 8 then x ⟨_, h⟩ ⟨_, h'⟩ else false)
  else false

lemma selLow_add (x y : Fin BAVC.tau → Fin 8 → Bool) (c : ℕ) :
    selLow (x + y) c = selLow x c + selLow y c := by
  unfold selLow; split_ifs <;> simp [Bool.add_eq_xor]

lemma ite_add_bool (a b : Bool) (z : GF128) :
    (if a + b then z else 0) = (if a then z else 0) + (if b then z else 0) := by
  cases a <;> cases b <;> simp [Bool.add_eq_xor, CharTwo.add_self_eq_zero]

/-- The assembly on the 128 used bits. -/
def maskLin (T : CrtTables) (v : Fin 128 → Bool) : GF128 :=
  ∑ k : Fin 128, if v k then maskCol T k else 0

lemma formHom_ite (l : ℕ) (b : Bool) (x : GF128) :
    formHom l (if b then x else 0) = zb b * formHom l x := by
  cases b <;> simp

theorem maskLin_injective {T : CrtTables} (hT : maskInvOk T = true) :
    Function.Injective (maskLin T) := by
  have hf : ∀ k c : Fin 128, form (maskInv.getD k 0) (maskCol T c) = (c.val == k.val) := by
    intro k c
    simp only [maskInvOk, List.all_eq_true, List.mem_range, beq_iff_eq] at hT
    have := hT k k.isLt c c.isLt
    simpa using this
  intro v v' h
  funext k
  have key := congrArg (formHom (maskInv.getD k 0)) h
  simp only [maskLin, map_sum, formHom_ite] at key
  have hfk : ∀ c : Fin 128, formHom (maskInv.getD k 0) (maskCol T c) = if c = k then 1 else 0 := by
    intro c
    show zb _ = _
    rw [hf k c]
    rcases eq_or_ne c k with rfl | hc
    · simp
    · rw [beq_eq_false_iff_ne.2 (Fin.val_ne_iff.2 hc)]
      simp [hc]
  simp only [hfk, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte] at key
  cases hv : v k <;> cases hv' : v' k <;> simp_all

theorem maskLin_surjective {T : CrtTables} (hT : maskInvOk T = true) :
    Function.Surjective (maskLin T) :=
  ((Fintype.bijective_iff_injective_and_card _).2 ⟨maskLin_injective hT, by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, GF128.card_eq]⟩).2

/-- The assembly on the pad bits (17 bytes of `u_low` sources and the `u_hi` byte), additive. -/
def crtLin (T : CrtTables) : (Fin BAVC.tau → Fin 8 → Bool) × (Fin 8 → Bool) →+ GF128 where
  toFun x := ∑ c ∈ range 120, (if selLow x.1 c then maskCol T c else 0) +
    ∑ j : Fin 8, (if x.2 j then maskCol T (120 + j) else 0)
  map_zero' := by
    have : ∀ c, selLow 0 c = false := fun c => by unfold selLow; split_ifs <;> rfl
    simp [this]
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, selLow_add, ite_add_bool,
      Finset.sum_add_distrib]
    ring

lemma crtLin_bits (T : CrtTables) (l : Fin BAVC.tau → UInt8) (h : UInt8) :
    crtLin T (fun i => byteBits (l i), byteBits h) = crtVal T l h := by
  rw [crtVal_eq]
  simp only [crtLin, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  congr 1

theorem crtLin_surjective {T : CrtTables} (hT : maskInvOk T = true) :
    Function.Surjective (crtLin T) := by
  intro y
  obtain ⟨v, rfl⟩ := maskLin_surjective hT y
  refine ⟨(fun i b => if hb : b.val < BAVC.kOf i then
      v ⟨BAVC.bitOffset i + b, by have := pos_lt i.isLt hb; omega⟩ else false,
    fun j => v ⟨120 + j, by omega⟩), ?_⟩
  simp only [crtLin, AddMonoidHom.coe_mk, ZeroHom.coe_mk, maskLin]
  rw [Fin.sum_univ_add (a := 120) (b := 8)]
  congr 1

/-- **One CRT mask is uniform**: `(u_low pads, u_hi byte) ↦ u_mask[m]` is balanced. -/
theorem balanced_crtVal {T : CrtTables} (hT : maskInvOk T = true) :
    Balanced (fun x : (Fin BAVC.tau → UInt8) × UInt8 => crtVal T x.1 x.2) := by
  let e : (Fin BAVC.tau → UInt8) × UInt8 ≃ (Fin BAVC.tau → Fin 8 → Bool) × (Fin 8 → Bool) :=
    Equiv.prodCongr (Equiv.arrowCongr (Equiv.refl _) byteBitsEquiv) byteBitsEquiv
  refine ((balanced_addHom (crtLin T) (crtLin_surjective hT) 0).equiv_comp e).congr fun x => ?_
  simp only [Function.comp_apply, add_zero]
  exact (crtLin_bits T x.1 x.2).symm

end

end VoleMole.ZK
