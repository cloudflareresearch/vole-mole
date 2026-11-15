import VoleMole.ZK.HopsH4Pt
import VoleMole.ZK.HopsH4Perm
import VoleMole.ZK.IdealCipherPtPerm

/-!
# Hop H4 at points with AES as random permutations: charged at points and at values

`hide_rom_query_pt` (`ZK/HopsH4Pt.lean`) charges H4 with **function** rows by the keys the
distinguisher reads at CTR blocks of the proof's `iv`. With **permutation** rows that charge is
false (`IC.inv_point_charge_fails`). Here is H4 with permutation rows (`PCipher`) and the charge of
`IC.puncturePtPm_real`: the keys read at a CTR block of `iv`, **or at a value of the hidden tree's
rows at their read points** (`hidVals`):

* the keys of the hidden nodes' children (the hidden children's keys, and the opened seeds),
* the hidden leaves' commitment blocks and VOLE blocks,
* the root's `u_hi` blocks.

A hidden node `n` is read at `PnB n`: its children's inputs, `u_hi`'s blocks for the root, the
commitment and VOLE blocks for a hidden leaf (`hidOfRows_congrPn`). Each hop replaces the row by a
uniform function on `PnB n` and costs `C(|PnB n|, 2)/2¹²⁸` more for a collision of the replacement
(`|PnB n| ≤ 4 + nHi + VOLE_COL_BLOCKS`, `card_PnB_le`). The fully replaced experiment reads uniform
function rows at the hidden nodes, so the last step of the function-row proof (`final_close`)
applies for every permutation table (`hidden_final_close`); no switching term.

**`hide_rom_query_ptPm`**: for a consistent reader `Q` of at most `qm` charged keys
(`221·qm < 2¹²⁸`),

    |Pr_real[A] − Pr_ideal[A]| ≤ (221·(4607 + E_real[#keys read at CTR blocks of iv or at hidVals])
                                  + 221·C(4 + nHi + VOLE_COL_BLOCKS, 2)) / (2¹²⁸ − 221·qm).

`hidVals` is a function of the real root seed and table (the hidden tree), not of the hidden part
`Hidden p` alone: the hidden children's keys are not revealed at all, and the VOLE blocks only
through the pads (with the opened leaves' blocks and, in a proof, the witness).
-/

open Finset

set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

variable [VoleMole.Verifier.HasPrg]
set_option linter.unusedSectionVars false

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.Privacy VoleMole.ZK.IC

variable (p : Params) (iv delta : ByteArray)

/-! ## The read points of the hidden rows -/

/-- The commitment and VOLE blocks of node `n`, if it is a hidden leaf. -/
def leafPts (n : ℕ) : Finset Blk :=
  (univ.filter fun i : Fin BAVC.tau => hLeaf delta i = n).biUnion fun i =>
    (range 2).image (comPt iv i) ∪ (range p.voleColBlocks).image (volePt iv i)

/-- **The points at which the hidden part reads node `n`'s row**: its children's inputs, the
`u_hi` blocks for the root, the commitment and VOLE blocks for a hidden leaf. -/
def PnB (n : ℕ) : Finset Blk :=
  (range 2).image (fun b => xIn iv (2 * n + 1 + b)) ∪ (if n = 0 then hiSet p iv else ∅) ∪
    leafPts p iv delta n

lemma xIn_mem_PnB {c : ℕ} (hc : c ≠ 0) : xIn iv c ∈ PnB p iv delta ((c - 1) / 2) := by
  refine mem_union_left _ (mem_union_left _ (mem_image.2 ⟨(c - 1) % 2, mem_range.2 (by omega), ?_⟩))
  congr 1
  omega

lemma comPt_mem_PnB (i : Fin BAVC.tau) {b : ℕ} (hb : b < 2) :
    comPt iv i b ∈ PnB p iv delta (hLeaf delta i) :=
  mem_union_right _ (mem_biUnion.2 ⟨i, mem_filter.2 ⟨mem_univ _, rfl⟩,
    mem_union_left _ (mem_image.2 ⟨b, mem_range.2 hb, rfl⟩)⟩)

lemma volePt_mem_PnB (i : Fin BAVC.tau) {j : ℕ} (hj : j < p.voleColBlocks) :
    volePt iv i j ∈ PnB p iv delta (hLeaf delta i) :=
  mem_union_right _ (mem_biUnion.2 ⟨i, mem_filter.2 ⟨mem_univ _, rfl⟩,
    mem_union_right _ (mem_image.2 ⟨j, mem_range.2 hj, rfl⟩)⟩)

lemma hiPt_mem_PnB {j : ℕ} (hj : j < nHi p) : hiPt iv j ∈ PnB p iv delta 0 :=
  mem_union_left _ (mem_union_right _ (by
    simp only [↓reduceIte]
    exact mem_image.2 ⟨j, mem_range.2 hj, rfl⟩))

/-- Every read point is a CTR block of `iv`. -/
lemma inY_of_mem_PnB {n : ℕ} {z : Blk} (hz : z ∈ PnB p iv delta n) : InY iv z := by
  simp only [PnB, leafPts, mem_union, mem_image, mem_range, mem_biUnion, mem_filter, mem_univ,
    true_and] at hz
  rcases hz with (⟨b, -, rfl⟩ | hz) | ⟨i, -, ⟨b, -, rfl⟩ | ⟨j, -, rfl⟩⟩
  · exact xIn_inY iv _
  · split_ifs at hz
    · obtain ⟨j, -, rfl⟩ := mem_image.1 hz
      exact ⟨_, _, rfl⟩
    · exact absurd hz (notMem_empty _)
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

lemma card_leafFilter_le (n : ℕ) : (univ.filter fun i : Fin BAVC.tau => hLeaf delta i = n).card ≤ 1 := by
  refine card_le_one.2 fun i hi i' hi' => ?_
  have e : hLeaf delta i = hLeaf delta i' := (mem_filter.1 hi).2.trans (mem_filter.1 hi').2.symm
  exact Fin.ext (treePos_inj i.isLt (deltaIndex_lt delta _) i'.isLt (deltaIndex_lt delta _) e).1

/-- **A node is read at most at `4 + nHi + VOLE_COL_BLOCKS` points.** -/
lemma card_PnB_le (n : ℕ) : (PnB p iv delta n).card ≤ 4 + nHi p + p.voleColBlocks := by
  unfold PnB
  have h1 : ((range 2).image (fun b => xIn iv (2 * n + 1 + b))).card ≤ 2 :=
    card_image_le.trans (by simp)
  have h2 : (if n = 0 then hiSet p iv else ∅).card ≤ nHi p := by
    split_ifs
    · exact card_image_le.trans (card_range _).le
    · simp
  have h3 : (leafPts p iv delta n).card ≤ 2 + p.voleColBlocks := by
    unfold leafPts
    refine card_biUnion_le.trans ?_
    calc ∑ i ∈ univ.filter (fun i : Fin BAVC.tau => hLeaf delta i = n),
          ((range 2).image (comPt iv i) ∪ (range p.voleColBlocks).image (volePt iv i)).card
        ≤ ∑ _i ∈ univ.filter (fun i : Fin BAVC.tau => hLeaf delta i = n), (2 + p.voleColBlocks) :=
          sum_le_sum fun i _ => (card_union_le _ _).trans (add_le_add
            (card_image_le.trans (card_range _).le) (card_image_le.trans (card_range _).le))
      _ ≤ 1 * (2 + p.voleColBlocks) := by
          rw [sum_const, smul_eq_mul]
          exact Nat.mul_le_mul_right _ (card_leafFilter_le delta n)
      _ = 2 + p.voleColBlocks := one_mul _
  have := card_union_le ((range 2).image (fun b => xIn iv (2 * n + 1 + b)) ∪
    (if n = 0 then hiSet p iv else ∅)) (leafPts p iv delta n)
  have := card_union_le ((range 2).image (fun b => xIn iv (2 * n + 1 + b)))
    (if n = 0 then hiSet p iv else ∅)
  omega

/-- **The hidden part reads a hidden row only at its points**, and the other rows whole. -/
theorem hidOfRows_congrPn (ρ ρ' : ℕ → Blk → Blk)
    (hsec : ∀ m < nN, hid delta m = true → ∀ z ∈ PnB p iv delta m, ρ m z = ρ' m z)
    (hns : ∀ m < nN, ¬ hid delta m = true → ρ m = ρ' m) :
    hidOfRows p iv delta ρ = hidOfRows p iv delta ρ' := by
  have hleaf : ∀ i : Fin BAVC.tau, ∀ z ∈ PnB p iv delta (hLeaf delta i),
      ρ (hLeaf delta i) z = ρ' (hLeaf delta i) z := fun i =>
    hsec _ (hLeaf_lt delta i.isLt) (hid_hLeaf delta i.isLt)
  have h3 : usR p iv ρ = usR p iv ρ' := by
    unfold usR
    refine Array.map_congr_left fun i hi => ?_
    have hi := Array.mem_range.1 hi
    refine congrArg bytesOfWords ?_
    unfold smallR
    refine List.foldl_ext _ _ _ fun acc j hj => ?_
    have hj := List.mem_range.1 hj
    by_cases hjd : j = BAVC.deltaIndex delta i
    · subst hjd
      dsimp only
      rw [show BAVC.treePos i (BAVC.deltaIndex delta i) = hLeaf delta i from rfl]
      refine congrArg (xorWords acc) (congrArg wordsOf (prgR_congr fun j' hj' => ?_))
      exact hleaf ⟨i, hi⟩ _ (volePt_mem_PnB p iv delta ⟨i, hi⟩ hj')
    · dsimp only
      have hn := treePos_not_mem delta hi hj hjd
      have hnh : ¬ hid delta (BAVC.treePos i j) = true := fun h =>
        hn ((mem_hidSet delta).2 ⟨treePos_lt hi hj, h⟩)
      rw [hns _ (treePos_lt hi hj) hnh]
  have h4 : prgR (ρ 0) iv (((1 : UInt32) <<< 31) - 1) 0 ((8 * p.nMask + 127) / 128) =
      prgR (ρ' 0) iv (((1 : UInt32) <<< 31) - 1) 0 ((8 * p.nMask + 127) / 128) :=
    prgR_congr fun j hj => hsec 0 (by decide) (hid_root delta) _ (hiPt_mem_PnB p iv delta hj)
  unfold hidOfRows
  rw [h3, h4]
  refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun k => ?_) rfl)
  · simp only
    exact congrArg (blk 32) (prgR_congr fun b hb => hleaf i _ (comPt_mem_PnB p iv delta i hb))
  · simp only
    split_ifs with hk
    · have hpos := oNode_pos delta hk
      exact hsec _ (oPar_lt delta ⟨k, hk⟩) ((mem_hidSet delta).1 (oPar_mem delta ⟨k, hk⟩)).2 _
        (xIn_mem_PnB p iv delta (c := oNode delta k) (by omega))
    · rfl

/-! ## The fully replaced experiment, for every table -/

/-- **With the hidden rows replaced by uniform functions, the hidden part is exactly the ideal
one, for every table** (the last step of `exper_final`). -/
theorem hidden_final_close (hp : SmallParams p) (E : Cipher) :
    Close 0 (fun c : Coins Blk Blk nN => hidOfRows p iv delta (rowAt (xIn iv) nN (hidSet delta) E c.2 c.1))
      (hiddenIdeal (p := p) delta) := by
  have h1 : Close 0 (fun R : Fin nN → Blk → Blk => finalF p iv delta E
      (partsEquiv p delta (restr p iv delta R))) (finalF p iv delta E) :=
    (((restr_close p iv delta hp).map fun a => finalF p iv delta E (partsEquiv p delta a)).trans
      (close_equiv (partsEquiv p delta) (finalF p iv delta E))).mono (by norm_num)
  have h2 := (close_prod_snd (α := Blk) (X := fun R : Fin nN → Blk → Blk =>
    finalF p iv delta E (partsEquiv p delta (restr p iv delta R)))).trans h1
  have h3 := h2.trans (final_close p iv delta hp E)
  have hfun : (fun c : Coins Blk Blk nN =>
      hidOfRows p iv delta (rowAt (xIn iv) nN (hidSet delta) E c.2 c.1)) =
      fun x : Blk × (Fin nN → Blk → Blk) =>
        finalF p iv delta E (partsEquiv p delta (restr p iv delta x.2)) :=
    funext fun c => hidOfRows_eq_finalF p iv delta hp E c.2 c.1
  rw [hfun]
  exact fun D => (h3 D).trans (le_of_eq (by norm_num))

/-! ## H4 at points and values with permutation rows -/

/-- **The values of the hidden tree's rows at their read points**, from the root seed and the
permutation table: the hidden nodes' children's keys, the commitment and VOLE blocks, `u_hi`'s
blocks. -/
def hidVals (π : PCipher) (seed : Blk) : Finset Blk :=
  valsP nN (fun n => hid delta n = true) (PnB p iv delta)
    (rowAt (xIn iv) nN ∅ (cf π) (fun _ _ => seed) seed)

/-- **The expected charge in the real experiment**: the keys read at a CTR block of `iv` or at a
value of the hidden tree (a uniform root seed and a uniform permutation table). -/
noncomputable def expVKeys (Q : Hidden p → PCipher → Finset (Blk × Blk)) : ℝ :=
  exP (Blk × PCipher) (fun s => ((vkeys (InY iv) (hidVals p iv delta s.2 s.1)
    (Q (hiddenOutE (cf s.2) p iv delta s.1) s.2) s.2).card : ℝ))

/-- The collision term of the hybrid: `221·C(4 + nHi + VOLE_COL_BLOCKS, 2)/2¹²⁸`. -/
noncomputable def collPm : ℝ := 221 * ((4 + nHi p + p.voleColBlocks).choose 2 : ℕ) / 2 ^ 128

/-- **H4 at points and values with AES as random permutations.** For a consistent reader `Q` of
the permutation table (`hQ`, `hQc`; an inverse query `(k, y)` is the forward point `(k, π_k⁻¹ y)`)
that reads at most `qm` keys at a CTR block of `iv` or at any value set's values (`hqm`), with
`221·qm < 2¹²⁸`:

    |Pr_real[A] − Pr_ideal[A]| ≤
      (221·(4607 + E_real[#keys read at CTR blocks of iv or at hidVals]) + 221·C(4 + nHi + VCB, 2))
        / (2¹²⁸ − 221·qm).

The expectation is over the root seed and the table in the real experiment (`expVKeys`). -/
theorem hide_rom_query_ptPm (hp : SmallParams p) (A : Hidden p → PCipher → Prop)
    (Q : Hidden p → PCipher → Finset (Blk × Blk))
    (hQ : ∀ o G G', (∀ kz ∈ Q o G, G kz.1 kz.2 = G' kz.1 kz.2) → (A o G ↔ A o G'))
    (hQc : ∀ o G G', (∀ kz ∈ Q o G, G kz.1 kz.2 = G' kz.1 kz.2) → Q o G = Q o G')
    {qm : ℕ} (hqm : ∀ o V G, (vkeys (InY iv) V (Q o G) G).card ≤ qm)
    (hsmall : 221 * (qm : ℝ) < 2 ^ 128) :
    |realPrPm (fun seed π => hiddenOutE (cf π) p iv delta seed) A -
        idealPrPm (hiddenIdeal (p := p) delta) A| ≤
      (221 * (4607 + expVKeys p iv delta Q) + 2 ^ 128 * collPm p) / (2 ^ 128 - 221 * qm) := by
  have hc : ((hidSet delta).card : ℝ) ≤ 221 := by exact_mod_cast hidSet_card delta
  have hcK : (Fintype.card Blk : ℝ) = 2 ^ 128 := by exact_mod_cast card_blk
  have hs : ((range nN).filter (fun n => hid delta n = true)).card * (qm : ℝ) < Fintype.card Blk := by
    rw [hcK]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)) hsmall
  have h := puncturePtPm_real (x := xIn iv) (N := nN) (P := InY iv) (fun n => hid delta n = true)
    (PnB p iv delta) (fun n hn hs h0 => hid_parent delta (by omega) hn hs)
    (fun n _ _ h0 m hm hmn hp => xIn_sib iv hm h0 hmn hp) (xIn_inY iv)
    (fun m z hz => inY_of_mem_PnB p iv delta hz) (fun c hc => xIn_mem_PnB p iv delta hc)
    (hidOfRows p iv delta) (fun n hn hs h0 ρ y => hidOfRows_point p iv delta hn h0 hs ρ y)
    (fun ρ ρ' hsec hns => hidOfRows_congrPn p iv delta ρ ρ' hsec hns) A Q hQ hQc hqm hs
  have e : ((range nN).filter fun n => hid delta n = true) = hidSet delta := rfl
  rw [e] at h
  -- the real experiment
  let eC : Coins Blk Blk nN × PCipher ≃ (Blk × PCipher) × (Fin nN → Blk → Blk) :=
    { toFun := fun c => ((c.1.1, c.2), c.1.2)
      invFun := fun c => ((c.1.1, c.2), c.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hreal : pr (Coins Blk Blk nN × PCipher)
      (fun c => A (hidOfRows p iv delta (rowAt (xIn iv) nN ∅ (cf c.2) c.1.2 c.1.1)) c.2) =
      realPrPm (fun seed π => hiddenOutE (cf π) p iv delta seed) A := by
    have h0 := pr_equiv eC (fun c => A (hiddenOutE (cf c.1.2) p iv delta c.1.1) c.1.2)
    rw [pr_prod_fst (fun s : Blk × PCipher => A (hiddenOutE (cf s.2) p iv delta s.1) s.2)] at h0
    rw [realPrPm, ← h0]
    refine pr_congr fun c => ?_
    show _ ↔ A (hidOfRows p iv delta (rowAt (xIn iv) nN ∅ (cf c.2) (fun _ _ => c.1.1) c.1.1)) c.2
    rw [rowAt_empty (cf c.2) c.1.2 (fun _ _ => c.1.1) c.1.1]
  have hEx : exP (Coins Blk Blk nN × PCipher) (fun c =>
      ((vkeys (InY iv) (valsP nN (fun n => hid delta n = true) (PnB p iv delta)
        (rowAt (xIn iv) nN ∅ (cf c.2) c.1.2 c.1.1))
        (Q (hidOfRows p iv delta (rowAt (xIn iv) nN ∅ (cf c.2) c.1.2 c.1.1)) c.2) c.2).card : ℝ)) =
      expVKeys p iv delta Q := by
    let f : Blk × PCipher → ℝ := fun s => ((vkeys (InY iv) (hidVals p iv delta s.2 s.1)
      (Q (hiddenOutE (cf s.2) p iv delta s.1) s.2) s.2).card : ℝ)
    have h1 : expVKeys p iv delta Q = exP (Coins Blk Blk nN × PCipher) (fun c => f (eC c).1) := by
      rw [exP_equiv eC (fun z => f z.1), exP_prod_fst (β := Fin nN → Blk → Blk) f]
      rfl
    rw [h1]
    refine congrArg (exP _) (funext fun c => ?_)
    show _ = ((vkeys (InY iv) (valsP nN (fun n => hid delta n = true) (PnB p iv delta)
      (rowAt (xIn iv) nN ∅ (cf c.2) (fun _ _ => c.1.1) c.1.1))
      (Q (hidOfRows p iv delta (rowAt (xIn iv) nN ∅ (cf c.2) (fun _ _ => c.1.1) c.1.1)) c.2)
        c.2).card : ℝ)
    rw [rowAt_empty (cf c.2) c.1.2 (fun _ _ => c.1.1) c.1.1]
  -- the fully replaced experiment
  have hfin : |pr (Coins Blk Blk nN × PCipher)
      (fun c => A (hidOfRows p iv delta (rowAt (xIn iv) nN (hidSet delta) (cf c.2) c.1.2 c.1.1)) c.2) -
      idealPrPm (hiddenIdeal (p := p) delta) A| ≤ 0 :=
    abs_pr_prod_sub_le' (fun c : Coins Blk Blk nN × PCipher =>
        A (hidOfRows p iv delta (rowAt (xIn iv) nN (hidSet delta) (cf c.2) c.1.2 c.1.1)) c.2)
      (fun h : Hidden p × PCipher => A (hiddenIdeal (p := p) delta h.1) h.2)
      fun π => hidden_final_close p iv delta hp (cf π) fun o => A o π
  have hfin' := sub_eq_zero.1 (abs_nonpos_iff.1 hfin)
  rw [hreal, hfin', hEx] at h
  refine h.trans ?_
  -- the numbers
  have hE : 0 ≤ expVKeys p iv delta Q := exP_nonneg fun _ => Nat.cast_nonneg _
  have hden : (0 : ℝ) < 2 ^ 128 - 221 * qm := by linarith
  have hC : ((∑ m ∈ hidSet delta, (PnB p iv delta m).card.choose 2 : ℕ) : ℝ) ≤
      2 ^ 128 * collPm p := by
    unfold collPm
    rw [mul_div_cancel₀ _ (by positivity), Nat.cast_sum]
    calc (∑ m ∈ hidSet delta, ((PnB p iv delta m).card.choose 2 : ℕ) : ℝ)
        ≤ ∑ _m ∈ hidSet delta, (((4 + nHi p + p.voleColBlocks).choose 2 : ℕ) : ℝ) :=
          sum_le_sum fun m _ => by exact_mod_cast Nat.choose_le_choose 2 (card_PnB_le p iv delta m)
      _ = (hidSet delta).card * (((4 + nHi p + p.voleColBlocks).choose 2 : ℕ) : ℝ) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ 221 * (((4 + nHi p + p.voleColBlocks).choose 2 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)
  have hN' : nN = 4607 := rfl
  have hN : ((nN : ℕ) : ℝ) = 4607 := by rw [hN']; norm_num
  have hnum : ((hidSet delta).card : ℝ) * ((nN : ℕ) + expVKeys p iv delta Q) +
      ((∑ m ∈ hidSet delta, (PnB p iv delta m).card.choose 2 : ℕ) : ℝ) ≤
      221 * (4607 + expVKeys p iv delta Q) + 2 ^ 128 * collPm p := by
    rw [hN]
    have := mul_le_mul_of_nonneg_right hc (by linarith : (0 : ℝ) ≤ 4607 + expVKeys p iv delta Q)
    linarith
  have hcoll : (0 : ℝ) ≤ collPm p :=
    div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (by norm_num)
  have hnum0 : (0 : ℝ) ≤ 221 * (4607 + expVKeys p iv delta Q) + 2 ^ 128 * collPm p := by
    have : (0 : ℝ) ≤ 2 ^ 128 * collPm p := mul_nonneg (by norm_num) hcoll
    linarith
  have hd : (2 : ℝ) ^ 128 - 221 * qm ≤ 2 ^ 128 - ((hidSet delta).card : ℝ) * qm := by
    have := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg (α := ℝ) qm)
    linarith
  rw [hcK]
  exact div_le_div₀ hnum0 hnum hden hd

end VoleMole.ZK.Sim
