import VoleMole.ZK.HopsH4Ideal
import VoleMole.ZK.IdealCipherPerm

/-!
# Hop H4 with AES as uniformly random permutations (`lean/docs/zk.md` §10.1)

`hide_rom_query` (`ZK/HopsH4Ideal.lean`) proves BAVC hiding with the cipher a table of uniform
*functions* (the PRF view). Here the cipher is a table `π : Blk → Equiv.Perm Blk` of independent
uniform **permutations** (`PCipher`), the BAVC is computed with its rows (`hiddenOutE (cf π)`), and
the distinguisher reads whole permutation rows at `q` keys, which subsumes forward and inverse
queries.

* **The GGM hybrid with permutation rows** (`hide_puncture_perm`, from `IC.puncturePm`): a hidden
  node's row becomes an independent uniform permutation, one node at a time in heap order. The
  node's value is its parent's (replaced) permutation at the node's input, and the rest of the
  experiment reads that permutation only at the sibling's input and, for the root, at the `u_hi`
  blocks (`rdH`, at most `nHi + 1` inputs; `hidOfRows_rd`). So the value is uniform over at least
  `2¹²⁸ − (nHi + 1)` values given the rest: each of the `≤ 221` hops costs
  `(4607 + q) / (2¹²⁸ − (nHi + 1))`.
* **The switching term** (`restr_closePm`, from `IC.close_evalPts`): after the hybrid the hidden
  part reads the replaced permutations at distinct points (`pts`, as in the PRF view). These are
  samples without replacement inside each row. Every hidden internal node's row is read at most
  at one point (its opened child, `oPar_inj`), so only the `τ = 17` hidden leaves (two commitment
  blocks and `VOLE_COL_BLOCKS` VOLE blocks each) and the root (its `nHi` `u_hi` blocks and at most
  one opened child) have collisions: `switchEps p = (17·C(2 + VOLE_COL_BLOCKS, 2) +
  C(nHi + 1, 2)) / 2¹²⁸` (`grpH`, `grpH_cov`, `grpH_sum`).
* **`hide_rom_query_perm`**: `221·(4607 + q)/(2¹²⁸ − (nHi + 1)) + switchEps p`.
-/

open Finset

-- (The coin and output types are large products: their `Fintype` instances exceed the default
-- size, and the fallback `FinEnum` instances do not unify with the generic ones.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

variable [VoleMole.Verifier.HasPrg]
set_option linter.unusedSectionVars false

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.Privacy VoleMole.ZK.IC

/-- **The cipher as uniformly random permutations**: a permutation of the blocks per key. -/
abbrev PCipher := Blk → Equiv.Perm Blk

/-! ## What the rest reads of a hidden node's parent -/

/-- The root's `u_hi` blocks. -/
def hiSet (p : Params) (iv : ByteArray) : Finset Blk := (range (nHi p)).image (hiPt iv)

/-- **The inputs of node `n`'s parent row read besides `n`'s own**: the sibling's input and, if
the parent is the root, the `u_hi` blocks. -/
def rdH (p : Params) (iv : ByteArray) (n : ℕ) : Finset Blk :=
  ((range (n + 2)).filter fun m => m ≠ 0 ∧ m ≠ n ∧ (m - 1) / 2 = (n - 1) / 2).image (xIn iv) ∪
    (if (n - 1) / 2 = 0 then hiSet p iv else ∅)

lemma rdH_card (p : Params) (iv : ByteArray) (n : ℕ) : (rdH p iv n).card ≤ nHi p + 1 := by
  unfold rdH
  refine (card_union_le _ _).trans ?_
  have h1 : ((range (n + 2)).filter fun m => m ≠ 0 ∧ m ≠ n ∧ (m - 1) / 2 = (n - 1) / 2).card ≤ 1 := by
    refine card_le_one.2 fun a ha b hb => ?_
    simp only [mem_filter, mem_range] at ha hb
    omega
  have h2 : (if (n - 1) / 2 = 0 then hiSet p iv else ∅).card ≤ nHi p := by
    split_ifs
    · exact card_image_le.trans (card_range _).le
    · simp
  have h3 : (((range (n + 2)).filter fun m => m ≠ 0 ∧ m ≠ n ∧ (m - 1) / 2 = (n - 1) / 2).image
      (xIn iv)).card ≤ 1 := card_image_le.trans h1
  omega

lemma xIn_not_mem_rdH (p : Params) (iv : ByteArray) {n : ℕ} (hn : n < nN) (hn0 : n ≠ 0) :
    xIn iv n ∉ rdH p iv n := by
  unfold rdH
  rw [mem_union, not_or]
  constructor
  · rw [mem_image]
    rintro ⟨m, hm, e⟩
    simp only [mem_filter] at hm
    exact xIn_sib iv hm.2.1 hn0 hm.2.2.1 hm.2.2.2 e
  · split_ifs with hq
    · unfold hiSet
      rw [mem_image]
      rintro ⟨j, -, e⟩
      exact blkCtr_ne_of_roles iv (r := .mask) (s := .ggm) (by decide) mask_tweak
        (ggm_tweak (par_lt_internal hn)) e
    · simp

lemma xIn_mem_rdH (p : Params) (iv : ByteArray) {n m : ℕ} (hn0 : n ≠ 0) (hm : m ≠ 0) (hmn : m ≠ n)
    (hpm : (m - 1) / 2 = (n - 1) / 2) : xIn iv m ∈ rdH p iv n :=
  mem_union_left _ (mem_image.2 ⟨m, mem_filter.2 ⟨mem_range.2 (by omega), hm, hmn, hpm⟩, rfl⟩)

/-- **The hidden part reads a hidden node's parent row only at `rdH`**: the opened seeds are the
other children's values, `u_hi` is the root's row at the mask tweak, the leaves are not parents. -/
theorem hidOfRows_rd (p : Params) (iv delta : ByteArray) {n : ℕ} (hn : n < nN) (hn0 : n ≠ 0)
    (hh : hid delta n = true) (ρ ρ' : ℕ → Blk → Blk)
    (hoff : ∀ m, m ≠ (n - 1) / 2 → ρ m = ρ' m)
    (hon : ∀ y ∈ rdH p iv n, ρ ((n - 1) / 2) y = ρ' ((n - 1) / 2) y) :
    hidOfRows p iv delta ρ = hidOfRows p iv delta ρ' := by
  set q := (n - 1) / 2 with hqdef
  have hq : q < BAVC.numLeaves - 1 := par_lt_internal hn
  have hleaf : ∀ m, BAVC.numLeaves - 1 ≤ m → ρ m = ρ' m := fun m hm => hoff m (by omega)
  have h1 : ∀ i : Fin BAVC.tau, ρ (hLeaf delta i) = ρ' (hLeaf delta i) := fun i =>
    hleaf _ (hLeaf_ge _ _)
  have h3 : usR p iv ρ = usR p iv ρ' := by
    unfold usR
    refine Array.map_congr_left fun i _ => ?_
    rw [show (fun j => ρ (BAVC.treePos i j)) = fun j => ρ' (BAVC.treePos i j) from
      funext fun j => hleaf _ (treePos_ge _ _)]
  have h4 : prgR (ρ 0) iv (((1 : UInt32) <<< 31) - 1) 0 ((8 * p.nMask + 127) / 128) =
      prgR (ρ' 0) iv (((1 : UInt32) <<< 31) - 1) 0 ((8 * p.nMask + 127) / 128) := by
    by_cases hq0 : q = 0
    · refine prgR_congr fun j hj => ?_
      have := hon (hiPt iv j) (by
        unfold rdH
        refine mem_union_right _ ?_
        have hq0' : (n - 1) / 2 = 0 := hq0
        simp only [hq0', ↓reduceIte]
        exact mem_image.2 ⟨j, mem_range.2 hj, rfl⟩)
      rw [hq0] at this
      exact this
    · rw [hoff 0 (Ne.symm hq0)]
  have h2 : ∀ k : Fin 105, k.val < openCount delta →
      ρ ((oNode delta k - 1) / 2) (xIn iv (oNode delta k)) =
        ρ' ((oNode delta k - 1) / 2) (xIn iv (oNode delta k)) := by
    intro k hk
    by_cases hpk : (oNode delta k - 1) / 2 = q
    · rw [hpk]
      have hpos := oNode_pos delta hk
      refine hon _ (xIn_mem_rdH p iv hn0 (by omega) (fun e => ?_) hpk)
      have := (openNodes_spec delta (oNode_mem delta hk)).1
      rw [e, hh] at this
      exact absurd this (by decide)
    · rw [hoff _ hpk]
  unfold hidOfRows
  rw [h3, h4]
  refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun k => ?_) rfl)
  · simp only [h1]
  · simp only
    split_ifs with hk
    · exact h2 k hk
    · rfl

lemma nHi_succ_lt (p : Params) (hp : SmallParams p) : nHi p + 1 < Fintype.card Blk := by
  rw [card_blk]
  have h := hp.2
  have : (2 : ℕ) ^ 32 < 2 ^ 128 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
  show (8 * p.nMask + 127) / 128 + 1 < 2 ^ 128
  omega

/-- **GGM puncturing of the BAVC tree with permutation rows**: replacing the permutations of all
nodes on the hidden paths by independent uniform permutations costs
`|hidden paths| · (2L − 1 + q) / (2¹²⁸ − (nHi + 1))` against a distinguisher of the hidden part that
reads the permutation table at `q` keys. -/
theorem hide_puncture_perm (p : Params) (hp : SmallParams p) (iv delta : ByteArray)
    (A : Hidden p → PCipher → Prop) (Q : Hidden p → PCipher → Finset Blk)
    (hQ : ∀ o G G', (∀ k ∈ Q o G, G k = G' k) → (A o G ↔ A o G')) {q : ℕ}
    (hq : ∀ o G, (Q o G).card ≤ q) :
    |experPm (xIn iv) nN ∅ (hidOfRows p iv delta) A -
        experPm (xIn iv) nN (hidSet delta) (hidOfRows p iv delta) A| ≤
      (hidSet delta).card * ((nN + q : ℕ) / ((2 ^ 128 - (nHi p + 1) : ℕ) : ℝ)) := by
  have h := puncturePm (x := xIn iv) (N := nN) (fun n => hid delta n = true)
    (fun n hn hs h0 => hid_parent delta (by omega) hn hs) (rdH p iv) (rdH_card p iv)
    (nHi_succ_lt p hp) (fun n hn _ h0 => xIn_not_mem_rdH p iv hn h0)
    (fun n _ _ h0 m hm hmn hpm => xIn_mem_rdH p iv h0 hm hmn hpm) (hidOfRows p iv delta)
    (fun n hn hs h0 ρ ρ' hoff hon => hidOfRows_rd p iv delta hn h0 hs ρ ρ' hoff hon)
    (hidOfRows_congr p iv delta) A Q hQ hq
  rw [card_blk] at h
  exact h

/-! ## The switching term -/

/-- No two opened nodes have the same parent (a hidden node has a hidden child). -/
lemma oPar_inj (delta : ByteArray) {k k' : ℕ} (hk : k < openCount delta)
    (hk' : k' < openCount delta) (h : (oNode delta k - 1) / 2 = (oNode delta k' - 1) / 2) :
    k = k' := by
  by_contra hne
  have hc : oNode delta k ≠ oNode delta k' := fun e => hne (oNode_inj delta hk hk' e)
  have h1 := openNodes_spec delta (oNode_mem delta hk)
  have h2 := openNodes_spec delta (oNode_mem delta hk')
  have p1 := oNode_pos delta hk
  have p2 := oNode_pos delta hk'
  have hint := hid_internal delta (par_lt_internal (oNode_lt delta hk))
  rw [h1.2] at hint
  rcases (by omega : (oNode delta k = 2 * ((oNode delta k - 1) / 2) + 1 ∧
      oNode delta k' = 2 * ((oNode delta k - 1) / 2) + 2) ∨
      (oNode delta k = 2 * ((oNode delta k - 1) / 2) + 2 ∧
      oNode delta k' = 2 * ((oNode delta k - 1) / 2) + 1)) with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [← e1, ← e2, h1.1, h2.1] at hint
    exact absurd hint (by decide)
  · rw [← e1, ← e2, h1.1, h2.1] at hint
    exact absurd hint (by decide)

variable (p : Params) (iv delta : ByteArray)

/-- **The groups of points of one row**: a hidden leaf's commitment and VOLE blocks; the root's
`u_hi` blocks with the opened children of the root. -/
def grpH : Fin BAVC.tau ⊕ Unit → Finset (PtIdx p delta)
  | .inl i => univ.image (Sum.elim (fun b : Fin 2 => (.inl (i, b) : PtIdx p delta))
      (fun j : Fin p.voleColBlocks => .inr (.inr (.inl (i, j)))))
  | .inr _ => univ.image (fun j : Fin (nHi p) => (.inr (.inr (.inr j)) : PtIdx p delta)) ∪
      (univ.filter fun k : Fin (openCount delta) => (oNode delta k - 1) / 2 = 0).image
        (fun k => (.inr (.inl k) : PtIdx p delta))

/-- **Two points of the same row lie in a common group.** -/
theorem grpH_cov : ∀ i j : PtIdx p delta, i ≠ j → (pts p iv delta i).1 = (pts p iv delta j).1 →
    ∃ g, i ∈ grpH p delta g ∧ j ∈ grpH p delta g := by
  intro i j hij h
  have hL : BAVC.numLeaves - 1 = 2303 := rfl
  have mc : ∀ (i : Fin BAVC.tau) (b : Fin 2),
      (.inl (i, b) : PtIdx p delta) ∈ grpH p delta (.inl i) := fun i b =>
    mem_image.2 ⟨.inl b, mem_univ _, rfl⟩
  have mv : ∀ (i : Fin BAVC.tau) (b : Fin p.voleColBlocks),
      (.inr (.inr (.inl (i, b))) : PtIdx p delta) ∈ grpH p delta (.inl i) := fun i b =>
    mem_image.2 ⟨.inr b, mem_univ _, rfl⟩
  have mh : ∀ j : Fin (nHi p), (.inr (.inr (.inr j)) : PtIdx p delta) ∈ grpH p delta (.inr ()) :=
    fun j => mem_union_left _ (mem_image.2 ⟨j, mem_univ _, rfl⟩)
  have mo : ∀ k : Fin (openCount delta), (oNode delta k - 1) / 2 = 0 →
      (.inr (.inl k) : PtIdx p delta) ∈ grpH p delta (.inr ()) := fun k hk =>
    mem_union_right _ (mem_image.2 ⟨k, mem_filter.2 ⟨mem_univ _, hk⟩, rfl⟩)
  have hli : ∀ i i' : Fin BAVC.tau, hLeaf delta i = hLeaf delta i' → i = i' := fun i i' e =>
    Fin.ext (treePos_inj i.isLt (deltaIndex_lt delta i) i'.isLt (deltaIndex_lt delta i') e).1
  have hlo : ∀ (i : Fin BAVC.tau) (k : Fin (openCount delta)),
      hLeaf delta i ≠ (oNode delta k - 1) / 2 := fun i k e => by
    have := hLeaf_ge delta i
    have := par_lt_internal (oNode_lt delta k.isLt)
    omega
  have hl0 : ∀ i : Fin BAVC.tau, hLeaf delta i ≠ 0 := fun i e => by
    have := hLeaf_ge delta i
    omega
  rcases i with ⟨i1, b1⟩ | k1 | ⟨i1, b1⟩ | j1 <;> rcases j with ⟨i2, b2⟩ | k2 | ⟨i2, b2⟩ | j2 <;>
    simp only [pts, Fin.mk.injEq] at h
  all_goals first
    | exact absurd h (hlo _ _)
    | exact absurd h.symm (hlo _ _)
    | exact absurd h (hl0 _)
    | exact absurd h.symm (hl0 _)
    | exact ⟨_, mo _ h, mh _⟩
    | exact ⟨_, mh _, mo _ h.symm⟩
    | exact ⟨_, mh _, mh _⟩
    | exact (hij (by rw [Fin.ext (oPar_inj delta k1.isLt k2.isLt h)])).elim
    | (obtain rfl := hli _ _ h
       first
        | exact ⟨_, mc _ _, mc _ _⟩
        | exact ⟨_, mc _ _, mv _ _⟩
        | exact ⟨_, mv _ _, mc _ _⟩
        | exact ⟨_, mv _ _, mv _ _⟩)

lemma grpH_card_inl (i : Fin BAVC.tau) : (grpH p delta (.inl i)).card ≤ 2 + p.voleColBlocks := by
  refine card_image_le.trans ?_
  rw [card_univ, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]

lemma grpH_card_inr (u : Unit) : (grpH p delta (.inr u)).card ≤ nHi p + 1 := by
  refine (card_union_le _ _).trans (add_le_add ?_ ?_)
  · exact card_image_le.trans (by rw [card_univ, Fintype.card_fin])
  · refine card_image_le.trans (card_le_one.2 fun a ha b hb => ?_)
    exact Fin.ext (oPar_inj delta a.isLt b.isLt ((mem_filter.1 ha).2.trans (mem_filter.1 hb).2.symm))

lemma grpH_sum : (∑ g, (grpH p delta g).card.choose 2) ≤
    BAVC.tau * (2 + p.voleColBlocks).choose 2 + (nHi p + 1).choose 2 := by
  rw [Fintype.sum_sum_type]
  refine add_le_add ?_ ?_
  · calc ∑ i : Fin BAVC.tau, (grpH p delta (.inl i)).card.choose 2
        ≤ ∑ _i : Fin BAVC.tau, (2 + p.voleColBlocks).choose 2 :=
          sum_le_sum fun i _ => Nat.choose_le_choose 2 (grpH_card_inl p delta i)
      _ = _ := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  · rw [Fintype.sum_unique]
    exact Nat.choose_le_choose 2 (grpH_card_inr p delta _)

/-- **The PRP/PRF switching term of the hidden paths**: `(17·C(2 + VOLE_COL_BLOCKS, 2) +
C(nHi + 1, 2)) / 2¹²⁸` (the hidden leaves' rows and the root's row; every other hidden row is read
at most once). -/
noncomputable def switchEps (p : Params) : ℝ :=
  ((BAVC.tau * (2 + p.voleColBlocks).choose 2 + (nHi p + 1).choose 2 : ℕ) : ℝ) / 2 ^ 128

/-- **The replacement permutations at the points are `switchEps`-close to uniform.** -/
theorem restr_closePm (hp : SmallParams p) :
    Close (switchEps p) (fun R : Fin nN → Equiv.Perm Blk => restr p iv delta (cf R))
      (id : (PtIdx p delta → Blk) → _) := by
  have h1 := close_evalPts (pts p iv delta) (pts_injective p hp iv delta)
  have h2 := pr_not_injPts_le (pts p iv delta) (grpH p delta) (grpH_cov p iv delta)
  refine (h1.mono (h2.trans ?_)).congr (fun _ => rfl) (fun _ => rfl)
  rw [card_blk, show ((2 ^ 128 : ℕ) : ℝ) = 2 ^ 128 by norm_num]
  unfold switchEps
  exact div_le_div_of_nonneg_right (by exact_mod_cast grpH_sum p delta) (by positivity)

/-- **The fully punctured experiment with permutation rows is `switchEps`-close to the ideal
one.** -/
theorem exper_finalPm (hp : SmallParams p) (A : Hidden p → PCipher → Prop) :
    |experPm (xIn iv) nN (hidSet delta) (hidOfRows p iv delta) A -
      idealPrPm (hiddenIdeal (p := p) delta) A| ≤ switchEps p := by
  refine experPm_close _ _ _ (fun π => ?_) A
  have h1 : Close (switchEps p) (fun R : Fin nN → Equiv.Perm Blk => finalF p iv delta (cf π)
      (partsEquiv p delta (restr p iv delta (cf R)))) (finalF p iv delta (cf π)) :=
    (((restr_closePm p iv delta hp).map fun a => finalF p iv delta (cf π) (partsEquiv p delta a)).trans
      (close_equiv (partsEquiv p delta) (finalF p iv delta (cf π)))).mono (by norm_num)
  have h2 := (close_prod_snd (α := Blk) (X := fun R : Fin nN → Equiv.Perm Blk =>
    finalF p iv delta (cf π) (partsEquiv p delta (restr p iv delta (cf R))))).trans h1
  have h3 := h2.trans (final_close p iv delta hp (cf π))
  have hfun : (fun c : PCoins Blk nN =>
      hidOfRows p iv delta (rowAt (xIn iv) nN (hidSet delta) (cf π) (cf c.2) c.1)) =
      fun x : Blk × (Fin nN → Equiv.Perm Blk) =>
        finalF p iv delta (cf π) (partsEquiv p delta (restr p iv delta (cf x.2))) :=
    funext fun c => hidOfRows_eq_finalF p iv delta hp (cf π) (cf c.2) c.1
  rw [hfun]
  exact h3.mono (by norm_num)

/-! ## Hop H4 with permutation rows -/

/-- **H4 with AES as uniformly random permutations, against a distinguisher that reads whole
permutation rows**: with the BAVC's cipher the rows of a uniform permutation table `π`
(`hiddenOutE (cf π)`), if `A` reads `π` at most at `q` keys (whole permutations, so forward and
inverse queries; `hQ`, `hq`), its advantage between the hidden part of a commitment from a uniform
root seed and the ideal hidden part with an independent table is at most

    221·(4607 + q) / (2¹²⁸ − (nHi + 1)) + (17·C(2 + VOLE_COL_BLOCKS, 2) + C(nHi + 1, 2)) / 2¹²⁸,

for every `iv` and `Δ` (`nHi = ⌈8·nMask/128⌉`, the root's `u_hi` blocks). The first term is the
GGM hybrid (key guessing; a hidden node's value is fresh in its parent's permutation, which the
rest reads at `≤ nHi + 1` inputs), the second the switching term of the hidden leaves' and the
root's rows. -/
theorem hide_rom_query_perm (hp : SmallParams p) (A : Hidden p → PCipher → Prop)
    (Q : Hidden p → PCipher → Finset Blk)
    (hQ : ∀ o G G', (∀ k ∈ Q o G, G k = G' k) → (A o G ↔ A o G')) {q : ℕ}
    (hq : ∀ o G, (Q o G).card ≤ q) :
    |realPrPm (fun seed π => hiddenOutE (cf π) p iv delta seed) A -
        idealPrPm (hiddenIdeal (p := p) delta) A| ≤
      221 * (4607 + q) / ((2 ^ 128 - (nHi p + 1) : ℕ) : ℝ) + switchEps p := by
  have h := hide_puncture_perm p hp iv delta A Q hQ hq
  rw [experPm_empty] at h
  have h2 := exper_finalPm p iv delta hp A
  have hc : ((hidSet delta).card : ℝ) ≤ 221 := by exact_mod_cast hidSet_card delta
  have hn : ((nN + q : ℕ) : ℝ) = 4607 + q := by push_cast; rfl
  have hpos : (0 : ℝ) ≤ ((nN + q : ℕ) : ℝ) / ((2 ^ 128 - (nHi p + 1) : ℕ) : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have h3 : ((hidSet delta).card : ℝ) * (((nN + q : ℕ) : ℝ) / ((2 ^ 128 - (nHi p + 1) : ℕ) : ℝ)) ≤
      221 * (4607 + q) / ((2 ^ 128 - (nHi p + 1) : ℕ) : ℝ) := by
    rw [mul_div_assoc, ← hn]
    exact mul_le_mul_of_nonneg_right hc hpos
  exact (abs_sub_le _ _ _).trans (add_le_add (h.trans h3) h2)

end VoleMole.ZK.Sim
