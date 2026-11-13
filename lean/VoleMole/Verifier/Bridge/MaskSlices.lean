import VoleMole.Verifier.Bridge.CrtComplete
import VoleMole.Verifier.Bridge.Chain
import VoleMole.Seed.SliceDecode

/-!
# Bridge: the executable verifier's CRT masks on slices

`lean/docs/security/pomfrit-lemmap-tight.md` §6.2 (Lemma S2), §6A. The class extractor needs two
facts about the verifier's responses as functions of the challenge, with the commitments fixed:
the response is affine on every slice of a set of trees with the same label rows (`AffineOn`), and
its increments along such a set are affine in the blocks of another such set (`TwoLabelOn`).
`Seed/KOSUnique.lean` and `Seed/SliceDecode.lean` prove both for a model of one gate
(`translateOn_gate_slice`, `twoLabel_gate`). This file proves that the executable verifier's
masks (`crtReconstructAt`, `Verifier/VOLE.lean`) are sums of such gates and of per-tree terms, for
any tables `T`, any gate hash `h5` and any committed keys.

* `col_bit`: column `p_i + b` of ConvertToVOLE at the blocks `Δ`, row `r`, is
  `V_{i,b}[r] + Δ_{i,b}·u^{(i)}[r]` (`treeColumns_affine`).
* `tree_form`: the tree part `r̃_m · W_TREE` of mask `m` is `Σ_i treeTerm m i (Δ_i)`, and
  `treeTerm m i` is affine in `Δ_i` (`treeTerm_translate`; `polyMod_xor`).
* `label_form`: the label of gate `e` is `C₀_e + Σ_i γ_{i,e}(Δ_i)·ℓ_i`, with `ℓ_i` (`labOf`) the
  128 label rows of `u^{(i)}` and `γ_{i,e}` (`gamHom`) the additive bit `⟨G[p_i + ·][e], Δ_i⟩`.
* `qMask_form`: mask `m` is `Σ_i treeTerm m i (Δ_i) + Σ_{e < N_MULT} gateF m e Δ`, where
  `gateF m e` is the gate model: a function of the label, plus the selection bit `Σ_i γ_{i,e}(Δ_i)`
  times a constant (the `c_mult` bit).
* **`chain_affineOn`**, **`chain_twoLabelOn`**: for a chain of the executable verifier
  (`Bridge/Chain.lean`), `AffineOn` on the slices of a set of trees with the same label rows and
  `TwoLabelOn` for two disjoint such sets. No hypothesis on the hash or on `c_mult`.
* `chain_claim4_lab`: `Claim4Hyp` for the label rows (the rows `o … o + 127` of the lifted
  response; they are hashed rows, so `KOSGood` gives their slopes).

No `sorry`, no `axiom`.
-/

open Finset

namespace VoleMole.Verifier.Bridge

variable [VoleMole.Verifier.HasPrg]
set_option linter.unusedSectionVars false

open VoleMole.Arith VoleMole.Verifier VoleMole.SeedExtraction VoleMole.Seed

noncomputable section

/-! ## Bits and field elements -/

/-- The field element with coefficients `f k`, `k < 128`. -/
def gfBits (f : ℕ → ZMod 2) : GF128 := ∑ k ∈ range 128, gf2 (f k) * CrtCheck.natGF (2 ^ k)

lemma gfBits_congr {f f' : ℕ → ZMod 2} (h : ∀ k < 128, f k = f' k) : gfBits f = gfBits f' :=
  Finset.sum_congr rfl fun k hk => by rw [h k (mem_range.1 hk)]

lemma gfNat_testBit (a : GF128) (k : ℕ) :
    (CrtCheck.gfNat a).testBit k =
      if k < 64 then a.lo.toNat.testBit k else a.hi.toNat.testBit (k - 64) := by
  rw [CrtCheck.gfNat, add_comm, Nat.testBit_two_pow_mul_add _ a.lo.toNat_lt]

/-- A block is the sum of its bits. -/
lemma toGF_eq_gfBits (w : W128) : w.toGF = gfBits fun k => zb (w.bit k) := by
  conv_lhs => rw [CrtCheck.gf_eq_sum w.toGF]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk := mem_range.1 hk
  rw [gfNat_testBit, CrtCheck.gf2_zb_mul, W128.bit_eq _ hk]
  rfl

lemma gf2_mul_eq_ite (x : ZMod 2) (a : GF128) : gf2 x * a = if x = 1 then a else 0 := by
  rcases (by decide : ∀ y : ZMod 2, y = 0 ∨ y = 1) x with rfl | rfl <;> simp

lemma gf_add_self (a : GF128) : a + a = 0 := CharTwo.add_self_eq_zero a

/-! ## Columns -/

section Cols

variable (p : Params) (iv : ByteArray) (corr : ℕ → ByteArray) (key : ℕ → ℕ → ByteArray)

lemma zb_dbitOf (Δ : Blocks) (i : Fin BAVC.tau) (b : Fin (BAVC.kOf i)) :
    zb (dbitOf Δ (BAVC.bitOffset i + b)) = Δ i b :=
  congrFun (congrFun (blocksOf_dbitOf Δ) i) b

/-- **ConvertToVOLE at the blocks `Δ`**: column `p_i + b`, row `r`, is
`V_{i,b}[r] + Δ_{i,b}·u^{(i)}[r]`. -/
theorem col_bit (Δ : Blocks) (i : Fin BAVC.tau) (b : Fin (BAVC.kOf i)) {r : ℕ}
    (hr : r < 64 * (p.colBytes / 8)) :
    zb (wbit (convertToVoleAt p (dbitOf Δ) corr iv key)[BAVC.bitOffset i + b]! r) =
      smallVoleV p iv i (key i) b r + Δ i b * smallVoleU p iv i (corr i) (key i) r := by
  rw [convertToVoleAt_col _ _ _ _ _ i.isLt b.isLt, treeColumns_affine _ _ _ _ _ _ b.isLt hr,
    testBit_hiddenIndex _ _ b.isLt, zb_dbitOf]

/-! ## The tree part -/

/-- Bit `d` of `X^{b+t} mod M_i`. -/
def pmBit (T : CrtTables) (i b t d : ℕ) : ZMod 2 :=
  zb ((polyMod ((1 : UInt64) <<< (b + t).toUInt64) T.mI[i]!).toNat.testBit d)

/-- The contribution of tree `i` to the tree part of mask `m`, as a function of its block. -/
def treeTerm (T : CrtTables) (m : ℕ) (i : Fin BAVC.tau) (x : Fin (BAVC.kOf i) → ZMod 2) : GF128 :=
  ∑ d : Fin (BAVC.kOf i), gf2 (∑ t : Fin (BAVC.kOf i), ∑ b : Fin (BAVC.kOf i),
    (smallVoleV p iv i (key i) b (p.correctionRows + 8 * m + t) +
      x b * smallVoleU p iv i (corr i) (key i) (p.correctionRows + 8 * m + t)) * pmBit T i b t d) *
    T.wTree[BAVC.bitOffset i + d]!.toGF

/-- The tree terms are affine in the block. -/
lemma treeTerm_translate (T : CrtTables) (m : ℕ) (i : Fin BAVC.tau)
    (a b c : Fin (BAVC.kOf i) → ZMod 2) :
    treeTerm p iv corr key T m i (a + (c - b)) =
      treeTerm p iv corr key T m i a +
        (treeTerm p iv corr key T m i c - treeTerm p iv corr key T m i b) := by
  simp only [treeTerm]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← sub_mul, ← add_mul, ← map_sub, ← map_add]
  congr 2
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b' _ => ?_
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- **The tree part of mask `m`** is a sum of per-tree terms. -/
theorem tree_form (T : CrtTables) (Δ : Blocks) {m : ℕ} (hm : m < p.nMask) :
    (W128.rowMul (rTildeOf T ((Array.range 8).map fun t =>
      rowOf (convertToVoleAt p (dbitOf Δ) corr iv key) (p.correctionRows + 8 * m + t))).bit 120
        T.wTree).toGF = ∑ i : Fin BAVC.tau, treeTerm p iv corr key T m i (Δ i) := by
  rw [rowMul_toGF, sum_range_120]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun d _ => ?_
  rw [← CrtCheck.gf2_zb_mul]
  congr 2
  rw [rTildeOf_bit _ _ (pos_lt i.isLt d.isLt), treeOf_pos d.isLt, Nat.add_sub_cancel_left,
    zb_polyMod_rTildeIn _ _ _ _ (kOf_le _),
    ← Fin.sum_univ_eq_sum_range (fun t => ∑ b ∈ range (BAVC.kOf i), _) (BAVC.kOf i)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Fin.sum_univ_eq_sum_range _ (BAVC.kOf i)]
  refine Finset.sum_congr rfl fun b _ => ?_
  have ht8 : (t : ℕ) < 8 := lt_of_lt_of_le t.isLt (kOf_le _)
  rw [getElem!_range_map _ _ ht8, rowOf_bit _ _ (by have := pos_lt i.isLt b.isLt; omega),
    col_bit p iv corr key Δ i b (maskRow_lt p hm ht8)]
  rfl

/-! ## The gate labels -/

/-- The label vector of tree `i`: the 128 label rows of `u^{(i)}`. -/
def labOf (i : Fin BAVC.tau) : GF128 :=
  gfBits fun k => smallVoleU p iv i (corr i) (key i) (p.labelRowOffset + k)

/-- The `Δ`-independent part of the label rows of column `p_i + b`. -/
def topV (i : Fin BAVC.tau) (b : ℕ) : GF128 :=
  gfBits fun k => smallVoleV p iv i (key i) b (p.labelRowOffset + k)

/-- The label rows of column `p_i + b` at the blocks `Δ`: `topV + Δ_{i,b}·ℓ_i`. -/
lemma top_form (hlab : p.labelRowOffset + 128 ≤ p.correctionRows) (Δ : Blocks) (i : Fin BAVC.tau)
    (b : Fin (BAVC.kOf i)) :
    (⟨wordAt (convertToVoleAt p (dbitOf Δ) corr iv key)[BAVC.bitOffset i + b]! p.labelRowOffset,
      wordAt (convertToVoleAt p (dbitOf Δ) corr iv key)[BAVC.bitOffset i + b]!
        (p.labelRowOffset + 64)⟩ : W128).toGF =
      topV p iv key i b + gf2 (Δ i b) * labOf p iv corr key i := by
  rw [toGF_eq_gfBits, topV, labOf, gfBits, gfBits, gfBits, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk := mem_range.1 hk
  have hrow : p.labelRowOffset + k < 64 * (p.colBytes / 8) :=
    lt_of_lt_of_le (by omega) (correctionRows_lt p)
  have hbit : zb ((⟨wordAt (convertToVoleAt p (dbitOf Δ) corr iv key)[BAVC.bitOffset i + b]!
      p.labelRowOffset, wordAt (convertToVoleAt p (dbitOf Δ) corr iv key)[BAVC.bitOffset i + b]!
        (p.labelRowOffset + 64)⟩ : W128).bit k) =
      smallVoleV p iv i (key i) b (p.labelRowOffset + k) +
        Δ i b * smallVoleU p iv i (corr i) (key i) (p.labelRowOffset + k) := by
    rw [W128.bit_eq _ hk, ← col_bit p iv corr key Δ i b hrow]
    split
    · rw [ZK.Sim.wordAt_testBit _ _ ‹_›]
    · rw [ZK.Sim.wordAt_testBit _ _ (by omega),
        show p.labelRowOffset + 64 + (k - 64) = p.labelRowOffset + k by omega]
  rw [hbit, map_add, map_mul]
  ring

/-- The additive bit `γ_{i,e}(Δ_i) = ⟨G[p_i + ·][e], Δ_i⟩`. -/
def gamHom (T : CrtTables) (e : ℕ) (i : Fin BAVC.tau) : (Fin (BAVC.kOf i) → ZMod 2) →+ ZMod 2 :=
  ∑ b : Fin (BAVC.kOf i), (AddMonoidHom.mulRight (zb (wbit T.g[BAVC.bitOffset i + b]! e))).comp
    (Pi.evalAddMonoidHom _ b)

lemma gamHom_apply (T : CrtTables) (e : ℕ) (i : Fin BAVC.tau) (x : Fin (BAVC.kOf i) → ZMod 2) :
    gamHom T e i x = ∑ b : Fin (BAVC.kOf i), x b * zb (wbit T.g[BAVC.bitOffset i + b]! e) := by
  simp [gamHom]

/-- The `Δ`-independent part of the label of gate `e`. -/
def labC (T : CrtTables) (e : ℕ) : GF128 :=
  ∑ i : Fin BAVC.tau, ∑ b : Fin (BAVC.kOf i),
    gf2 (zb (wbit T.g[BAVC.bitOffset i + b]! e)) * topV p iv key i b

/-- **The label of gate `e`** at the blocks `Δ`: `C₀_e + Σ_i γ_{i,e}(Δ_i)·ℓ_i`. -/
theorem label_form (T : CrtTables) (hlab : p.labelRowOffset + 128 ≤ p.correctionRows)
    (Δ : Blocks) (e : ℕ) :
    (W128.rowMul (fun c => wbit T.g[c]! e) 120 ((Array.range 120).map fun c =>
      (⟨wordAt (convertToVoleAt p (dbitOf Δ) corr iv key)[c]! p.labelRowOffset,
        wordAt (convertToVoleAt p (dbitOf Δ) corr iv key)[c]! (p.labelRowOffset + 64)⟩ :
          W128))).toGF =
      labC p iv key T e +
        ∑ i : Fin BAVC.tau, if gamHom T e i (Δ i) = 1 then labOf p iv corr key i else 0 := by
  rw [rowMul_toGF, sum_range_120, labC, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← gf2_mul_eq_ite, gamHom_apply, map_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [getElem!_range_map _ _ (pos_lt i.isLt b.isLt), top_form p iv corr key hlab Δ i b,
    ← CrtCheck.gf2_zb_mul, map_mul]
  ring

/-- Bit `e` of `γ = Δ·G` at the blocks `Δ`. -/
lemma gamma_form (T : CrtTables) (Δ : Blocks) {e : ℕ} (he : e < 320) :
    zb (wbit (gammaOf T (dbitOf Δ)) e) = ∑ i : Fin BAVC.tau, gamHom T e i (Δ i) := by
  rw [zb_wbit_gammaOf _ _ he, sum_range_120]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gamHom_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [zb_and, zb_dbitOf]

/-! ## The gate hashes and the masks -/

/-- The gate hash of gate `e` at the label `L` (as a field element). -/
def gateHashW (h5 : ByteArray → ByteArray) (e : ℕ) (L : GF128) : UInt32 :=
  AES.getLE32 (h5 ((AES.pushLE32 iv e.toUInt32 ++ (⟨L.lo, L.hi⟩ : W128).toBytes).push 5)) 0

lemma gateHashes_get (h5 : ByteArray → ByteArray) (T : CrtTables) (cols : Array (Array UInt64))
    {e : ℕ} (he : e < p.nMult) :
    (gateHashes h5 p T iv cols)[e]! = gateHashW iv h5 e
      (W128.rowMul (fun c => wbit T.g[c]! e) 120 ((Array.range 120).map fun c =>
        (⟨wordAt cols[c]! p.labelRowOffset, wordAt cols[c]! (p.labelRowOffset + 64)⟩ :
          W128))).toGF := by
  have hlen : e < ((gateInputs p T iv cols).map h5).length := by
    simp [gateInputs, he]
  rw [gateHashes, ZK.Sim.gateWords_get _ hlen]
  simp only [gateInputs, List.getElem_map, List.getElem_range, gateHashW]
  rfl

/-- The hash part of gate `e` in mask `m`, as a function of the label. -/
def gateT (T : CrtTables) (h5 : ByteArray → ByteArray) (m e : ℕ) (L : GF128) : GF128 :=
  if (gateHashW iv h5 e L >>> m.toUInt32) &&& 1 == 1 then T.wGate[e]!.toGF else 0

/-- The `c_mult` part of gate `e` in mask `m`. -/
def gateCm (T : CrtTables) (cmult : ByteArray) (m e : ℕ) : GF128 :=
  if ((cmult.extract (m * p.nMultBytes) ((m + 1) * p.nMultBytes)).get! (e / 8) >>>
      (e % 8).toUInt8) &&& 1 == 1 then T.wGate[e]!.toGF else 0

/-- **The term of gate `e` in mask `m`**, in the form of the gate model
(`Seed.translateOn_gate_slice`, `Seed.twoLabel_gate`). -/
def gateF (T : CrtTables) (h5 : ByteArray → ByteArray) (cmult : ByteArray) (m e : ℕ)
    (Δ : Blocks) : GF128 :=
  gateT iv T h5 m e (labC p iv key T e +
      ∑ i : Fin BAVC.tau, if gamHom T e i (Δ i) = 1 then labOf p iv corr key i else 0) +
    if ∑ i : Fin BAVC.tau, gamHom T e i (Δ i) = 1 then gateCm p T cmult m e else 0

/-- **The CRT masks of the executable verifier**: mask `m` at the blocks `Δ` is a sum of per-tree
terms and of the gate terms. -/
theorem qMask_form (h5 : ByteArray → ByteArray) (T : CrtTables) (cmult : ByteArray)
    (hlab : p.labelRowOffset + 128 ≤ p.correctionRows) (Δ : Blocks) {m : ℕ} (hm : m < p.nMask) :
    (crtReconstructAt h5 p (dbitOf Δ) cmult T iv
      (convertToVoleAt p (dbitOf Δ) corr iv key)).qMask[m]!.toGF =
      ∑ i : Fin BAVC.tau, treeTerm p iv corr key T m i (Δ i) +
        ∑ e ∈ range p.nMult, gateF p iv corr key T h5 cmult m e Δ := by
  simp only [crtReconstructAt, crtReconstructWith]
  rw [getElem!_range_map _ _ hm, getElem!_range_map _ _ hm, toGF_xor,
    tree_form p iv corr key T Δ hm, rowMul_toGF]
  congr 1
  refine Finset.sum_congr rfl fun e he => ?_
  have he := mem_range.1 he
  have he320 : e < 320 := lt_of_lt_of_le he (by simp [Params.nMult])
  have hg := gamma_form T Δ he320
  rw [gateHashes_get p iv h5 T _ he, label_form p iv corr key T hlab Δ e, gateF, gateT, gateCm]
  generalize (∑ i : Fin BAVC.tau, gamHom T e i (Δ i)) = s at hg
  rcases (by decide : ∀ y : ZMod 2, y = 0 ∨ y = 1) s with rfl | rfl
  · have hγ : wbit (gammaOf T (dbitOf Δ)) e = false := by
      cases h : wbit (gammaOf T (dbitOf Δ)) e
      · rfl
      · rw [h] at hg; exact absurd hg (by decide)
    simp only [hγ, Bool.false_and, Bool.xor_false, zero_ne_one, ite_false, add_zero]
  · have hγ : wbit (gammaOf T (dbitOf Δ)) e = true := by
      cases h : wbit (gammaOf T (dbitOf Δ)) e
      · rw [h] at hg; exact absurd hg (by decide)
      · rfl
    simp only [hγ, Bool.true_and, ite_true]
    split_ifs <;> simp_all [gf_add_self]

end Cols

/-! ## Translations and two-label increments: generic lemmas -/

section Generic

variable {R : Type*} [AddCommGroup R]

lemma translateOn_mono {X : Type*} [AddCommGroup X] {S S' : Set X} {f : X → R}
    (h : TranslateOn S f) (hS : S' ⊆ S) : TranslateOn S' f :=
  fun Δ hΔ Δ₂ h₂ Δ₃ h₃ => h Δ (hS hΔ) Δ₂ (hS h₂) Δ₃ (hS h₃)

lemma translateOn_const_add {X : Type*} [AddCommGroup X] {S : Set X} {f : X → R}
    (h : TranslateOn S f) (c : R) : TranslateOn S fun Δ => c + f Δ :=
  fun Δ hΔ Δ₂ h₂ Δ₃ h₃ => by
    show c + f _ = c + f Δ + (c + f Δ₃ - (c + f Δ₂))
    rw [h Δ hΔ Δ₂ h₂ Δ₃ h₃]; abel

/-- A sum of per-tree functions, each affine in its block, commutes with translations. -/
lemma translateOn_trees (S : Set Blocks) (F : ∀ i : Fin BAVC.tau, (Fin (BAVC.kOf i) → ZMod 2) → R)
    (hF : ∀ i a b c, F i (a + (c - b)) = F i a + (F i c - F i b)) :
    TranslateOn S fun Δ => ∑ i, F i (Δ i) := fun Δ _ Δ₂ _ Δ₃ _ => by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => hF i _ _ _

/-- The two-label identity of `Seed.TwoLabelOn` for one function. -/
def TL (f : Blocks → R) (x δ g g' : Blocks) : Prop :=
  f (x + g + g' + δ) - f (x + g + g') - (f (x + g + δ) - f (x + g)) =
    f (x + g' + δ) - f (x + g') - (f (x + δ) - f x)

lemma TL.add {f f' : Blocks → R} {x δ g g' : Blocks} (h : TL f x δ g g') (h' : TL f' x δ g g') :
    TL (fun Δ => f Δ + f' Δ) x δ g g' := by
  unfold TL at *
  have e : ∀ a b c d a' b' c' d' : R,
      a + a' - (b + b') - (c + c' - (d + d')) = (a - b - (c - d)) + (a' - b' - (c' - d')) := by
    intros; abel
  rw [e, e, h, h']

lemma TL.const_add {f : Blocks → R} {x δ g g' : Blocks} (h : TL f x δ g g') (c : R) :
    TL (fun Δ => c + f Δ) x δ g g' := by
  unfold TL at *
  have e : ∀ a b c' d : R, c + a - (c + b) - (c + c' - (c + d)) = a - b - (c' - d) := by
    intros; abel
  rw [e, e, h]

lemma TL.sum {κ : Type*} (s : Finset κ) {f : κ → Blocks → R} {x δ g g' : Blocks}
    (h : ∀ k ∈ s, TL (f k) x δ g g') : TL (fun Δ => ∑ k ∈ s, f k Δ) x δ g g' := by
  unfold TL at *
  simp only [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k hk => h k hk

/-- A sum of per-tree functions has two-label increments when no tree moves in both `δ` and
`g`, `g'`. -/
lemma TL_trees (F : ∀ i : Fin BAVC.tau, (Fin (BAVC.kOf i) → ZMod 2) → R) {x δ g g' : Blocks}
    (h : ∀ i, δ i = 0 ∨ (g i = 0 ∧ g' i = 0)) : TL (fun Δ => ∑ i, F i (Δ i)) x δ g g' := by
  unfold TL
  simp only [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases h i with h0 | ⟨h1, h2⟩
  · simp [h0]
  · simp [h1, h2]

lemma dirs_disjoint {C T₁ : Finset (Fin BAVC.tau)} (hd : Disjoint C T₁) {δ g g' : Blocks}
    (hδ : δ ∈ dirs C) (hg : g ∈ dirs T₁) (hg' : g' ∈ dirs T₁) (i : Fin BAVC.tau) :
    δ i = 0 ∨ (g i = 0 ∧ g' i = 0) := by
  by_cases hi : i ∈ C
  · exact Or.inr ⟨hg i (Finset.disjoint_left.1 hd hi), hg' i (Finset.disjoint_left.1 hd hi)⟩
  · exact Or.inl (hδ i hi)

end Generic

/-! ## The gate terms are the gate model -/

section GateModel

variable (p : Params) (iv : ByteArray) (corr : ℕ → ByteArray) (key : ℕ → ℕ → ByteArray)
  (T : CrtTables) (h5 : ByteArray → ByteArray) (cmult : ByteArray) (m e : ℕ)

lemma gateF_translateOn {C : Finset (Fin BAVC.tau)} {ℓ : GF128}
    (hℓ : ∀ i ∈ C, labOf p iv corr key i = ℓ) (g : Blocks) :
    TranslateOn (slice C g) (gateF p iv corr key T h5 cmult m e) :=
  translateOn_gate_slice (R := GF128) gf_add_self gf_add_self (gamHom T e) (labOf p iv corr key)
    (labC p iv key T e) (gateT iv T h5 m e) (gateCm p T cmult m e) C hℓ g

lemma gateF_TL {C T₁ : Finset (Fin BAVC.tau)} (hd : Disjoint C T₁) {ℓ ℓ₁ : GF128}
    (hℓ : ∀ i ∈ C, labOf p iv corr key i = ℓ) (hℓ₁ : ∀ i ∈ T₁, labOf p iv corr key i = ℓ₁)
    {x δ g g' : Blocks} (hδ : δ ∈ dirs C) (hg : g ∈ dirs T₁) (hg' : g' ∈ dirs T₁) :
    TL (gateF p iv corr key T h5 cmult m e) x δ g g' :=
  twoLabel_gate (R := GF128) gf_add_self gf_add_self (gamHom T e) (labOf p iv corr key)
    (labC p iv key T e) (gateT iv T h5 m e) (gateCm p T cmult m e) C T₁ hd hℓ hℓ₁ x δ g g' hδ hg
    hg'

end GateModel

/-! ## The response of a chain -/

namespace Chain

variable (st : Statement) (ch : Chain) (T : CrtTables)

/-- The label rows of tree `i`: rows `o … o + 127` of the extractor's `u^{(i)}`. -/
def lab (i : Fin BAVC.tau) (j : Fin 128) : Bool :=
  uBit st.params ch.iv (ch.corr st) ch.keys i (st.params.labelRowOffset + j)

/-- The label rows of the committed response. -/
def Ql (j : Fin 128) (Δ : Blocks) : GF128 :=
  (ch.resp st T Δ).rows[st.params.labelRowOffset + (j : ℕ)]!.toGF

/-- The label vector of tree `i` as a field element (`labOf`). -/
def labV (i : Fin BAVC.tau) : GF128 := labOf st.params ch.iv (ch.corr st) ch.keys i

lemma labV_eq_of_lab_eq {i i' : Fin BAVC.tau} (h : ch.lab st i = ch.lab st i') :
    ch.labV st i = ch.labV st i' := by
  unfold labV labOf
  refine gfBits_congr fun k hk => ?_
  have := congrFun h ⟨k, hk⟩
  simp only [lab, uBit] at this
  generalize smallVoleU st.params ch.iv i (ch.corr st i) (ch.keys i)
    (st.params.labelRowOffset + k) = a at this ⊢
  generalize smallVoleU st.params ch.iv i' (ch.corr st i') (ch.keys i')
    (st.params.labelRowOffset + k) = b at this ⊢
  revert this
  rcases (by decide : ∀ y : ZMod 2, y = 0 ∨ y = 1) a with rfl | rfl <;>
    rcases (by decide : ∀ y : ZMod 2, y = 0 ∨ y = 1) b with rfl | rfl <;> simp

/-- The lifted rows of the committed response, per tree (`resp_row`). -/
lemma resp_row_form (Δ : Blocks) {r : ℕ} (hr : r < st.params.correctionRows) :
    (ch.resp st T Δ).rows[r]!.toGF = rowConst T st.params ch.iv ch.keys r +
      ∑ i, SeedExtraction.bit (uBit st.params ch.iv (ch.corr st) ch.keys i r) *
        blockLift (lift T) i (Δ i) := by
  have := resp_row ch.h5 T st.params (dbitOf Δ) (ch.corr st) (ch.pf st).cmult ch.iv ch.keys hr
  rw [blocksOf_dbitOf] at this
  exact this

/-- The masks of the committed response (`qMask_form`). -/
lemma resp_mask_form (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    (Δ : Blocks) {m : ℕ} (hm : m < st.params.nMask) :
    (ch.resp st T Δ).qMask[m]!.toGF =
      ∑ i : Fin BAVC.tau, treeTerm st.params ch.iv (ch.corr st) ch.keys T m i (Δ i) +
        ∑ e ∈ range st.params.nMult,
          gateF st.params ch.iv (ch.corr st) ch.keys T ch.h5 (ch.pf st).cmult m e Δ :=
  qMask_form st.params ch.iv (ch.corr st) ch.keys ch.h5 T (ch.pf st).cmult hlab Δ hm

/-- A lifted row of the committed response, on a set where the trees outside `known` are fixed. -/
lemma row_tree_form {A : Set Blocks} {known : Finset (Fin BAVC.tau)}
    (hL2 : ∀ i ∉ known, IsFixed A i) {r : ℕ} (hr : r < st.params.correctionRows) :
    ∃ c, ∀ Δ ∈ A, (ch.resp st T Δ).rows[r]!.toGF = c + ∑ i ∈ known,
      SeedExtraction.bit (uBit st.params ch.iv (ch.corr st) ch.keys i r) *
        blockLift (lift T) i (Δ i) := by
  classical
  rcases A.eq_empty_or_nonempty with hA0 | ⟨Δ₀, hΔ₀⟩
  · exact ⟨0, fun Δ hΔ => by simp [hA0] at hΔ⟩
  refine ⟨rowConst T st.params ch.iv ch.keys r + ∑ i ∈ univ.filter (· ∉ known),
    SeedExtraction.bit (uBit st.params ch.iv (ch.corr st) ch.keys i r) *
      blockLift (lift T) i (Δ₀ i), fun Δ hΔ => ?_⟩
  have hk : univ.filter (· ∈ known) = known := by ext; simp
  have hfix : ∑ i ∈ univ.filter (· ∉ known),
      SeedExtraction.bit (uBit st.params ch.iv (ch.corr st) ch.keys i r) *
        blockLift (lift T) i (Δ i) =
      ∑ i ∈ univ.filter (· ∉ known),
        SeedExtraction.bit (uBit st.params ch.iv (ch.corr st) ch.keys i r) *
          blockLift (lift T) i (Δ₀ i) :=
    Finset.sum_congr rfl fun i hi => by rw [hL2 i (Finset.mem_filter.1 hi).2 Δ hΔ Δ₀ hΔ₀]
  rw [ch.resp_row_form st T Δ hr, ← Finset.sum_filter_add_sum_filter_not univ (· ∈ known), hk,
    hfix]
  ring

/-- A lifted row commutes with translations, on every set. -/
lemma row_translateOn (S : Set Blocks) {r : ℕ} (hr : r < st.params.correctionRows) :
    TranslateOn S fun Δ => (ch.resp st T Δ).rows[r]!.toGF := by
  have h := translateOn_const_add (translateOn_trees S (fun i x =>
    SeedExtraction.bit (uBit st.params ch.iv (ch.corr st) ch.keys i r) *
      blockLift (lift T) i x) fun i a b c => by simp only [map_add, map_sub]; ring)
    (rowConst T st.params ch.iv ch.keys r)
  intro Δ hΔ Δ₂ h₂ Δ₃ h₃
  have := h Δ hΔ Δ₂ h₂ Δ₃ h₃
  simp only [← ch.resp_row_form st T _ hr] at this
  exact this

/-- **A mask commutes with translations on the slices of a set of trees with one label
vector** (Lemma S2 for the executable verifier). -/
lemma mask_translateOn (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    {C : Finset (Fin BAVC.tau)} {ℓ : GF128} (hℓ : ∀ i ∈ C, ch.labV st i = ℓ) (g : Blocks) {m : ℕ}
    (hm : m < st.params.nMask) :
    TranslateOn (slice C g) fun Δ => (ch.resp st T Δ).qMask[m]!.toGF := by
  have h := (translateOn_trees (slice C g)
    (fun i => treeTerm st.params ch.iv (ch.corr st) ch.keys T m i)
    (treeTerm_translate st.params ch.iv (ch.corr st) ch.keys T m)).add
    (TranslateOn.sum (range st.params.nMult) fun e _ =>
      gateF_translateOn st.params ch.iv (ch.corr st) ch.keys T ch.h5 (ch.pf st).cmult m e
        (fun i hi => hℓ i hi) g)
  intro Δ hΔ Δ₂ h₂ Δ₃ h₃
  have := h Δ hΔ Δ₂ h₂ Δ₃ h₃
  simp only [ch.resp_mask_form st T hlab _ hm]
  exact this

/-- **A mask has two-label increments** for two disjoint sets of trees, each with one label
vector. -/
lemma mask_TL (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    {C T₁ : Finset (Fin BAVC.tau)} (hd : Disjoint C T₁) {ℓ ℓ₁ : GF128}
    (hℓ : ∀ i ∈ C, ch.labV st i = ℓ) (hℓ₁ : ∀ i ∈ T₁, ch.labV st i = ℓ₁) {x δ g g' : Blocks}
    (hδ : δ ∈ dirs C) (hg : g ∈ dirs T₁) (hg' : g' ∈ dirs T₁) {m : ℕ}
    (hm : m < st.params.nMask) :
    TL (fun Δ => (ch.resp st T Δ).qMask[m]!.toGF) x δ g g' := by
  have h := (TL_trees (fun i => treeTerm st.params ch.iv (ch.corr st) ch.keys T m i)
    (x := x) (dirs_disjoint hd hδ hg hg')).add
    (TL.sum (range st.params.nMult) fun e _ =>
      gateF_TL st.params ch.iv (ch.corr st) ch.keys T ch.h5 (ch.pf st).cmult m e hd
        (fun i hi => hℓ i hi) (fun i hi => hℓ₁ i hi) hδ hg hg')
  unfold TL at h ⊢
  simp only [ch.resp_mask_form st T hlab _ hm]
  exact h

lemma row_TL {C T₁ : Finset (Fin BAVC.tau)} (hd : Disjoint C T₁) {x δ g g' : Blocks}
    (hδ : δ ∈ dirs C) (hg : g ∈ dirs T₁) (hg' : g' ∈ dirs T₁) {r : ℕ}
    (hr : r < st.params.correctionRows) :
    TL (fun Δ => (ch.resp st T Δ).rows[r]!.toGF) x δ g g' := by
  have h := (TL_trees (fun i y =>
    SeedExtraction.bit (uBit st.params ch.iv (ch.corr st) ch.keys i r) *
      blockLift (lift T) i y) (x := x) (dirs_disjoint hd hδ hg hg')).const_add
    (rowConst T st.params ch.iv ch.keys r)
  unfold TL at h ⊢
  simp only [ch.resp_row_form st T _ hr]
  exact h

/-- The hashed rows: the lifted rows, then the first `d − 1` masks. -/
lemma kosQ_apply (Δ : Blocks) (k : Fin (kosL st)) :
    ch.kosQ st T Δ k = if (k : ℕ) < st.params.correctionRows then
      (ch.resp st T Δ).rows[(k : ℕ)]!.toGF
    else (ch.resp st T Δ).qMask[(k : ℕ) - st.params.correctionRows]!.toGF := by
  split
  · rename_i h
    exact ch.kosQ_row st T Δ h
  · rename_i h
    have hk := k.isLt
    unfold kosL at hk
    have := ch.kosQ_mask st T Δ (i := (k : ℕ) - st.params.correctionRows) (by omega)
    rw [← this]
    congr 1
    exact Fin.ext (by simp; omega)

end Chain

/-- **Lemma S2 for the executable verifier**: the response of a chain is affine on every slice of
a set `C` of trees with the same label rows, within the challenges with given blocks outside
`S`. For any tables, gate hash and `c_mult`. -/
theorem chain_affineOn (st : Statement) (ch : Chain) (T : CrtTables)
    (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    {C : Finset (Fin BAVC.tau)} (hC : ∀ i ∈ C, ∀ i' ∈ C, ch.lab st i = ch.lab st i')
    (S : Finset (Fin BAVC.tau)) (hd g : Blocks) :
    AffineOn ({Δ : Blocks | ∀ i ∉ S, Δ i = hd i} ∩ slice C g) (ch.kosQ st T) (ch.kosD st T) := by
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ∀ i ∈ C, ch.labV st i = ℓ := by
    rcases C.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
    · exact ⟨0, fun i hi => absurd hi (Finset.notMem_empty i)⟩
    · exact ⟨ch.labV st i₀, fun i hi => ch.labV_eq_of_lab_eq st (hC i hi i₀ hi₀)⟩
  have hsub : {Δ : Blocks | ∀ i ∉ S, Δ i = hd i} ∩ slice C g ⊆ slice C g := Set.inter_subset_right
  refine affineOn_of_translateOn (fun Δ hΔ Δ₂ h₂ Δ₃ h₃ =>
    ⟨slice_translate (C := S) (g := hd) hΔ.1 h₂.1 h₃.1, slice_translate hΔ.2 h₂.2 h₃.2⟩)
    (translateOn_mono ?_ hsub) (translateOn_mono ?_ hsub)
  · intro Δ hΔ Δ₂ h₂ Δ₃ h₃
    funext k
    simp only [Pi.add_apply, Pi.sub_apply, Chain.kosQ_apply]
    split
    · rename_i h
      exact ch.row_translateOn st T _ h Δ hΔ Δ₂ h₂ Δ₃ h₃
    · have hk := k.isLt
      unfold Chain.kosL at hk
      exact ch.mask_translateOn st T hlab hℓ g
        (by unfold Params.nMask; omega) Δ hΔ Δ₂ h₂ Δ₃ h₃
  · intro Δ hΔ Δ₂ h₂ Δ₃ h₃
    funext j
    exact ch.mask_translateOn st T hlab hℓ g (by have := j.isLt; unfold Params.nMask; omega)
      Δ hΔ Δ₂ h₂ Δ₃ h₃

/-- **The two-label structure of the executable verifier's response**: for disjoint sets `C` and
`T₁` of trees, each with the same label rows, the increments of the response along the blocks of
`C` are affine in the blocks of `T₁`. For any tables, gate hash and `c_mult`. -/
theorem chain_twoLabelOn (st : Statement) (ch : Chain) (T : CrtTables)
    (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    {C T₁ : Finset (Fin BAVC.tau)} (hd : Disjoint C T₁)
    (hC : ∀ i ∈ C, ∀ i' ∈ C, ch.lab st i = ch.lab st i')
    (hT₁ : ∀ i ∈ T₁, ∀ i' ∈ T₁, ch.lab st i = ch.lab st i') (Sb : Set Blocks) :
    TwoLabelOn Sb C T₁ (ch.kosQ st T) (ch.kosD st T) := by
  have hex : ∀ D : Finset (Fin BAVC.tau), (∀ i ∈ D, ∀ i' ∈ D, ch.lab st i = ch.lab st i') →
      ∃ ℓ, ∀ i ∈ D, ch.labV st i = ℓ := by
    intro D hD
    rcases D.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
    · exact ⟨0, fun i hi => absurd hi (Finset.notMem_empty i)⟩
    · exact ⟨ch.labV st i₀, fun i hi => ch.labV_eq_of_lab_eq st (hD i hi i₀ hi₀)⟩
  obtain ⟨ℓ, hℓ⟩ := hex C hC
  obtain ⟨ℓ₁, hℓ₁⟩ := hex T₁ hT₁
  intro x _ δ hδ g hg g' hg'
  constructor
  · funext k
    simp only [Pi.sub_apply, Chain.kosQ_apply]
    split
    · rename_i h
      exact ch.row_TL st T hd hδ hg hg' h
    · have hk := k.isLt
      unfold Chain.kosL at hk
      exact ch.mask_TL st T hlab hd hℓ hℓ₁ hδ hg hg' (by unfold Params.nMask; omega)
  · funext j
    exact ch.mask_TL st T hlab hd hℓ hℓ₁ hδ hg hg'
      (by have := j.isLt; unfold Params.nMask; omega)

/-- **Claim 4's hypotheses for the label rows** of a chain of the executable verifier: as
`chain_claim4` for the witness rows. The label rows are lifted rows of the response, hashed by
the VOLE check, so `KOSGood` gives their slopes on `A`. -/
theorem chain_claim4_lab {T : CrtTables} (hT : liftInvOk T = true) (st : Statement) (ch : Chain)
    (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    {A : Finset Blocks} (hA : ∀ Δ ∈ A, ch.OnChain st T Δ) {S : Set Blocks}
    (hAS : (A : Set Blocks) ⊆ S)
    (hkos : Seed.KOSGood ch.kosCh S (lift T) (ch.kosQ st T) (ch.kosD st T))
    {known : Finset (Fin BAVC.tau)} (hL2 : ∀ i ∉ known, IsFixed (A : Set Blocks) i) :
    ∃ lStar : Fin 128 → GF128,
      Claim4Hyp (lift T) (A : Set Blocks) known (ch.lab st) (ch.Ql st T) lStar := by
  obtain ⟨uQ, vQ, hrow, -⟩ := chain_kos_affine T st ch hA hAS hkos
  refine ⟨fun j => uQ (st.params.labelRowOffset + j), lift_injective hT,
    fun j => ch.row_tree_form st T hL2 (by have := j.isLt; omega),
    fun j => ⟨vQ (st.params.labelRowOffset + j), fun Δ hΔ => ?_⟩, hL2⟩
  rw [Chain.Ql, hrow _ (by have := j.isLt; omega) Δ (Finset.mem_coe.1 hΔ), mul_comm]

end

end VoleMole.Verifier.Bridge
