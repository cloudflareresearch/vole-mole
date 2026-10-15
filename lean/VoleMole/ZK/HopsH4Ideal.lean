import VoleMole.ZK.HopsH4

/-!
# The punctured BAVC commitment is uniform (the last step of hop H4, ideal-cipher model)

In the experiment of `IC.puncture` with every node of the hidden paths replaced (`hidSet Δ`), the
hidden part `hidOfRows` reads the replacement rows at finitely many distinct points (`pts`):

* the hidden leaves' rows at their two commitment blocks (leaf tweak);
* the parents of the opened nodes at the opened nodes' inputs (the opened seeds; GGM tweak);
* the hidden leaves' rows at their VOLE blocks (VOLE tweak);
* the root's row at its `u_hi` blocks (mask tweak).

They are distinct (`pts_injective`: different nodes, or different tweak roles,
`Bridge.ctrBlock_ne_of_roles`, or different counters). The rows off the hidden paths depend on the
replacement rows only at the opened seeds (`IC.rowAt_congr_points`). So the hidden part is a
function of the cipher table and of the uniform values at these points, and for every table it is
exactly uniform (`final_close`): the commitments and the seeds are the values themselves, every
`u^{(i)}` is the opened leaves' part XOR the hidden leaf's VOLE blocks (`fold_xor_diff`), laid out
bijectively in the pads, and `u_hi` is a truncation of the root's blocks.

Assumes `SmallParams p` (fewer than `2³²` blocks per PRG call, so the CTR counters do not wrap),
true for every relation's parameters.
-/

open Finset

-- (The coin and output types are large products: their `Fintype` instances exceed the default
-- size, and the fallback `FinEnum` instances do not unify with the generic ones.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.Privacy VoleMole.ZK.IC

/-! ## Bytes of the PRG and of XOR folds -/

/-- Byte `t` of `prgR`: byte `t % 16` of block `t / 16`. -/
lemma prgR_get (r : Blk → Blk) (iv : ByteArray) (tw c : UInt32) {n t : ℕ} (ht : t < 16 * n) :
    (prgR r iv tw c n).get! t =
      r (blk 16 (AES.ctrBlock iv (c + (t / 16).toUInt32) tw)) ⟨t % 16, Nat.mod_lt _ (by norm_num)⟩ := by
  unfold prgR
  rw [get!_foldl_blocks (fun j => ba (r (blk 16 (AES.ctrBlock iv (c + j.toUInt32) tw)))) 16
    (fun _ => size_ba _) n t (by omega), get!_ba _ (Nat.mod_lt _ (by norm_num))]

lemma xor_cancel_mid (a a' w X : UInt8) : a ^^^ w ^^^ (a' ^^^ w) ^^^ X = a ^^^ a' ^^^ X := by
  rw [UInt8.xor_assoc a w, UInt8.xor_comm a' w, ← UInt8.xor_assoc w w a', UInt8.xor_self,
    UInt8.zero_xor]

lemma xor_swap_mid (a a' w w' : UInt8) : a ^^^ w ^^^ (a' ^^^ w') = a ^^^ a' ^^^ (w ^^^ w') := by
  simp only [UInt8.xor_assoc]
  rw [← UInt8.xor_assoc w a' w', UInt8.xor_comm w a', UInt8.xor_assoc]

/-- **The bytes of two XOR folds that differ in one summand.** -/
theorem fold_xor_diff (W W' : ℕ → Array UInt64) (s d : ℕ) {k : ℕ} (hk : k < 8 * s) :
    ∀ (l : List ℕ), l.Nodup → (∀ j ∈ l, (W j).size = s) → (∀ j ∈ l, (W' j).size = s) →
    (∀ j ∈ l, j ≠ d → W j = W' j) → ∀ acc acc' : Array UInt64, acc.size = s → acc'.size = s →
    (bytesOfWords (l.foldl (fun acc j => xorWords acc (W j)) acc)).get! k ^^^
      (bytesOfWords (l.foldl (fun acc j => xorWords acc (W' j)) acc')).get! k =
    (bytesOfWords acc).get! k ^^^ (bytesOfWords acc').get! k ^^^
      (if d ∈ l then (bytesOfWords (W d)).get! k ^^^ (bytesOfWords (W' d)).get! k else 0)
  | [], _, _, _, _, acc, acc', _, _ => by simp
  | j :: l, hnd, hW, hW', hag, acc, acc', ha, ha' => by
    simp only [List.foldl_cons]
    have hj := hW j (by simp)
    have hj' := hW' j (by simp)
    rw [fold_xor_diff W W' s d hk l (List.nodup_cons.1 hnd).2 (fun j h => hW j (by simp [h]))
      (fun j h => hW' j (by simp [h])) (fun j h => hag j (by simp [h])) _ _
      (by rw [xorWords_size, ha]) (by rw [xorWords_size, ha']),
      bytesOfWords_xorWords_get _ _ (by rw [ha, hj]) (by rw [ha]; exact hk),
      bytesOfWords_xorWords_get _ _ (by rw [ha', hj']) (by rw [ha']; exact hk)]
    by_cases hjd : j = d
    · subst hjd
      have hnot : j ∉ l := (List.nodup_cons.1 hnd).1
      simp only [hnot, ↓reduceIte, List.mem_cons_self, UInt8.xor_zero]
      exact xor_swap_mid _ _ _ _
    · rw [hag j (by simp) hjd]
      have : (d ∈ j :: l) ↔ d ∈ l := by simp [Ne.symm hjd]
      simp only [this]
      exact xor_cancel_mid _ _ _ _

/-! ## The points -/

/-- The parameters' PRG calls have fewer than `2³²` blocks (the CTR counters do not wrap). -/
def SmallParams (p : Params) : Prop :=
  p.voleColBlocks < 2 ^ 32 ∧ (8 * p.nMask + 127) / 128 < 2 ^ 32

/-- `SmallParams` holds for every relation's parameters (witnesses and degrees far below `2²⁴`). -/
theorem smallParams_of_le {p : Params} (hw : p.witnessBytes ≤ 2 ^ 24) (hd : p.qsDegree ≤ 2 ^ 24) :
    SmallParams p := by
  simp only [SmallParams, Params.voleColBlocks, Params.voleRows, Params.correctionRows,
    Params.witnessBits, Params.nMask]
  split <;> omega

/-- The number of `u_hi` blocks. -/
abbrev nHi (p : Params) : ℕ := (8 * p.nMask + 127) / 128

/-- Block `b` of the commitment of a hidden leaf of vector `i`. -/
def comPt (iv : ByteArray) (i b : ℕ) : Blk :=
  blk 16 (AES.ctrBlock iv (0 + b.toUInt32) (i + BAVC.numLeaves - 1).toUInt32)

/-- Block `j` of the VOLE PRG of a leaf of vector `i`. -/
def volePt (iv : ByteArray) (i j : ℕ) : Blk :=
  blk 16 (AES.ctrBlock iv (0 + j.toUInt32) (((1 : UInt32) <<< 31) + i.toUInt32))

/-- Block `j` of the root's `u_hi` PRG. -/
def hiPt (iv : ByteArray) (j : ℕ) : Blk :=
  blk 16 (AES.ctrBlock iv (0 + j.toUInt32) (((1 : UInt32) <<< 31) - 1))

/-- The points read off the replacement rows: commitments, opened seeds, VOLE blocks, `u_hi`. -/
abbrev PtIdx (p : Params) (delta : ByteArray) :=
  (Fin BAVC.tau × Fin 2) ⊕ (Fin (openCount delta) ⊕ ((Fin BAVC.tau × Fin p.voleColBlocks) ⊕ Fin (nHi p)))

lemma oPar_lt (delta : ByteArray) (k : Fin (openCount delta)) : (oNode delta k - 1) / 2 < nN := by
  have := oNode_lt delta k.isLt; omega

/-- **The points.** -/
def pts (p : Params) (iv delta : ByteArray) : PtIdx p delta → Fin nN × Blk
  | .inl ib => (⟨hLeaf delta ib.1, hLeaf_lt delta ib.1.isLt⟩, comPt iv ib.1 ib.2)
  | .inr (.inl k) => (⟨(oNode delta k - 1) / 2, oPar_lt delta k⟩, xIn iv (oNode delta k))
  | .inr (.inr (.inl ij)) => (⟨hLeaf delta ij.1, hLeaf_lt delta ij.1.isLt⟩, volePt iv ij.1 ij.2)
  | .inr (.inr (.inr j)) => (⟨0, by decide⟩, hiPt iv j)

lemma leaf_tw {i : ℕ} (hi : i < BAVC.tau) :
    (i + BAVC.numLeaves - 1).toUInt32.toNat ∈ Seed.Commitments.tweaks .leaf :=
  (leafCom_tweak .empty .empty hi).2

lemma vole_tw {i : ℕ} (hi : i < BAVC.tau) :
    (((1 : UInt32) <<< 31) + i.toUInt32).toNat ∈ Seed.Commitments.tweaks .vole := by
  rw [(vole_tweak hi).1]; exact (vole_tweak hi).2

lemma lt32_of_lt {a b : ℕ} (h : a < b) (hb : b < 2 ^ 32) : a < 2 ^ 32 := lt_trans h hb

/-- **The points are distinct.** -/
theorem pts_injective (p : Params) (hp : SmallParams p) (iv delta : ByteArray) :
    Function.Injective (pts p iv delta) := by
  have hL : BAVC.numLeaves - 1 = 2303 := rfl
  have hLg := hLeaf_ge delta
  have hinj : ∀ {i i' : ℕ}, i < BAVC.tau → i' < BAVC.tau → hLeaf delta i = hLeaf delta i' → i = i' :=
    fun hi hi' h => (treePos_inj hi (deltaIndex_lt delta _) hi' (deltaIndex_lt delta _) h).1
  have hpar : ∀ k : Fin (openCount delta), (oNode delta k - 1) / 2 < BAVC.numLeaves - 1 :=
    fun k => par_lt_internal (oNode_lt delta k.isLt)
  have hb2 : ∀ b : Fin 2, b.val < 2 ^ 32 := fun b => by have := b.isLt; omega
  intro a a' h
  rcases a with ⟨i, b⟩ | k | ⟨i, j⟩ | j <;> rcases a' with ⟨i', b'⟩ | k' | ⟨i', j'⟩ | j' <;>
    simp only [pts, Prod.mk.injEq, Fin.mk.injEq] at h <;> obtain ⟨h1, h2⟩ := h
  -- 1. commitment / commitment
  · obtain rfl := Fin.ext (hinj i.isLt i'.isLt h1)
    have := zero_add_toUInt32_inj (hb2 b) (hb2 b') (blkCtr_inj iv h2).1
    rw [Fin.ext this]
  -- 2. commitment / seed
  · have := hLg i; have := hpar k'; omega
  -- 3. commitment / VOLE
  · obtain rfl := Fin.ext (hinj i.isLt i'.isLt h1)
    exact absurd h2 (blkCtr_ne_of_roles iv (by decide) (leaf_tw i.isLt) (vole_tw i.isLt))
  -- 4. commitment / `u_hi`
  · have := hLg i; omega
  -- 5. seed / commitment
  · have := hLg i'; have := hpar k; omega
  -- 6. seed / seed
  · have hk := oNode_pos delta k.isLt
    have hk' := oNode_pos delta k'.isLt
    by_contra hne
    have hne' : oNode delta k ≠ oNode delta k' := fun e => hne (by
      rw [Fin.ext (oNode_inj delta k.isLt k'.isLt e)])
    exact xIn_sib iv (by omega) (by omega) hne' h1 h2
  -- 7. seed / VOLE
  · have := hLg i'; have := hpar k; omega
  -- 8. seed / `u_hi`
  · exfalso
    refine blkCtr_ne_of_roles iv (r := .ggm) (s := .mask) (c := 0 + ((oNode delta k - 1) % 2).toUInt32)
      (c' := 0 + j'.val.toUInt32) (by decide) (ggm_tweak (hpar k)) mask_tweak ?_
    rw [← xIn, h2, hiPt]
  -- 9. VOLE / commitment
  · obtain rfl := Fin.ext (hinj i.isLt i'.isLt h1)
    exact absurd h2.symm (blkCtr_ne_of_roles iv (by decide) (leaf_tw i.isLt) (vole_tw i.isLt))
  -- 10. VOLE / seed
  · have := hLg i; have := hpar k'; omega
  -- 11. VOLE / VOLE
  · obtain rfl := Fin.ext (hinj i.isLt i'.isLt h1)
    have := zero_add_toUInt32_inj (lt32_of_lt j.isLt hp.1) (lt32_of_lt j'.isLt hp.1)
      (blkCtr_inj iv h2).1
    rw [Fin.ext this]
  -- 12. VOLE / `u_hi`
  · have := hLg i; omega
  -- 13. `u_hi` / commitment
  · have := hLg i'; omega
  -- 14. `u_hi` / seed
  · exfalso
    refine blkCtr_ne_of_roles iv (r := .ggm) (s := .mask) (c := 0 + ((oNode delta k' - 1) % 2).toUInt32)
      (c' := 0 + j.val.toUInt32) (by decide) (ggm_tweak (hpar k')) mask_tweak ?_
    rw [← xIn, ← h2, hiPt]
  -- 15. `u_hi` / VOLE
  · have := hLg i'; omega
  -- 16. `u_hi` / `u_hi`
  · rw [Fin.ext (zero_add_toUInt32_inj (lt32_of_lt j.isLt hp.2) (lt32_of_lt j'.isLt hp.2)
      (blkCtr_inj iv h2).1)]

/-! ## The values at the points are uniform -/

variable (p : Params) (iv delta : ByteArray)

/-- The replacement rows at the points. -/
def restr (R : Fin nN → Blk → Blk) : PtIdx p delta → Blk :=
  fun a => R (pts p iv delta a).1 (pts p iv delta a).2

/-- **The replacement rows at the (distinct) points are uniform.** -/
theorem restr_close (hp : SmallParams p) :
    Close 0 (restr p iv delta) (id : (PtIdx p delta → Blk) → _) := by
  have h1 := close_restrict (K := Fin nN × Blk) (R := Blk) (pts_injective p hp iv delta)
  have h2 := close_equiv (Equiv.curry (Fin nN) Blk Blk).symm
    (fun g : Fin nN × Blk → Blk => g ∘ pts p iv delta)
  exact ((h2.trans h1).mono (by norm_num)).congr (fun _ => rfl) fun _ => rfl

/-- Rows taking the values `a` at the points (zero elsewhere). -/
noncomputable def rowsOf (a : PtIdx p delta → Blk) : Fin nN → Blk → Blk := by
  classical
  exact fun n z => if h : ∃ i, pts p iv delta i = (n, z) then a h.choose else 0

lemma rowsOf_pts (hp : SmallParams p) (a : PtIdx p delta → Blk) (i : PtIdx p delta) :
    rowsOf p iv delta a (pts p iv delta i).1 (pts p iv delta i).2 = a i := by
  classical
  have h : ∃ j, pts p iv delta j = ((pts p iv delta i).1, (pts p iv delta i).2) := ⟨i, rfl⟩
  simp only [rowsOf, h, dite_true]
  rw [pts_injective p hp iv delta h.choose_spec]

lemma restr_rowsOf (hp : SmallParams p) (a : PtIdx p delta → Blk) :
    restr p iv delta (rowsOf p iv delta a) = a :=
  funext fun i => rowsOf_pts p iv delta hp a i

/-- The parts of the values: commitments, opened seeds, VOLE blocks, `u_hi`. -/
abbrev Parts := (Fin BAVC.tau × Fin 2 → Blk) × ((Fin (openCount delta) → Blk) ×
  ((Fin BAVC.tau × Fin p.voleColBlocks → Blk) × (Fin (nHi p) → Blk)))

/-- The values as their parts. -/
def partsEquiv : (PtIdx p delta → Blk) ≃ Parts p delta :=
  (Equiv.sumArrowEquivProdArrow _ _ _).trans (Equiv.prodCongr (Equiv.refl _)
    ((Equiv.sumArrowEquivProdArrow _ _ _).trans (Equiv.prodCongr (Equiv.refl _)
      (Equiv.sumArrowEquivProdArrow _ _ _))))

/-! ## The fully punctured experiment reads the rows only at the points -/

lemma mem_hidSet {n : ℕ} : n ∈ hidSet delta ↔ n < nN ∧ hid delta n = true := by
  simp [hidSet]

lemma hLeaf_mem (i : Fin BAVC.tau) : hLeaf delta i ∈ hidSet delta :=
  (mem_hidSet delta).2 ⟨hLeaf_lt delta i.isLt, hid_hLeaf delta i.isLt⟩

lemma root_mem : 0 ∈ hidSet delta := (mem_hidSet delta).2 ⟨by decide, hid_root delta⟩

lemma treePos_not_mem {i j : ℕ} (hi : i < BAVC.tau) (hj : j < 2 ^ BAVC.kOf i)
    (hjd : j ≠ BAVC.deltaIndex delta i) : BAVC.treePos i j ∉ hidSet delta := by
  rw [mem_hidSet, hid_treePos delta hi hj]
  simp [hjd]

lemma oPar_mem (k : Fin (openCount delta)) : (oNode delta k - 1) / 2 ∈ hidSet delta :=
  (mem_hidSet delta).2 ⟨oPar_lt delta k, (openNodes_spec delta (oNode_mem delta k.isLt)).2⟩

lemma exists_oNode {c : ℕ} (hc : c ∈ BAVC.openNodes delta) :
    ∃ k < openCount delta, oNode delta k = c := by
  have hs := openNodes_size delta
  unfold oNode
  generalize BAVC.openNodes delta = nodes at hc hs
  obtain ⟨k, hk, hkc⟩ := Array.mem_iff_getElem.1 hc
  exact ⟨k, by omega, by rw [getElem!_pos nodes k hk, hkc]⟩

variable {p iv delta}

/-- The rows off the hidden paths agree when the replacement rows agree at the opened seeds. -/
lemma rows_off (E : Cipher) {R R' : Fin nN → Blk → Blk} (s s' : Blk)
    (h : ∀ k, restr p iv delta R (.inr (.inl k)) = restr p iv delta R' (.inr (.inl k))) :
    ∀ m < nN, m ∉ hidSet delta →
      rowAt (xIn iv) nN (hidSet delta) E R s m = rowAt (xIn iv) nN (hidSet delta) E R' s' m := by
  intro m hm hmS
  refine (rowAt_congr_points (root_mem delta) E R R' s s' (fun c hc hc0 hcS hp hpS => ?_) m hm hmS).1
  have hcid : hid delta c = false := by
    rw [mem_hidSet] at hcS; simpa [hc] using hcS
  have hpid := ((mem_hidSet delta).1 hpS).2
  have hmem := mem_openNodes delta (by omega) hc hcid hpid
  obtain ⟨k, hk', hok⟩ := exists_oNode delta hmem
  have := h ⟨k, hk'⟩
  simp only [restr, pts] at this
  have e : (⟨(c - 1) / 2, hp⟩ : Fin nN) = ⟨(oNode delta k - 1) / 2, oPar_lt delta ⟨k, hk'⟩⟩ :=
    Fin.ext (by simp [hok])
  rw [e, ← hok]
  exact this

lemma rowAt_hid (E : Cipher) (R : Fin nN → Blk → Blk) (s : Blk) {n : ℕ} (hn : n ∈ hidSet delta) :
    rowAt (xIn iv) nN (hidSet delta) E R s n = R ⟨n, ((mem_hidSet delta).1 hn).1⟩ :=
  rowAt_of_mem hn _

/-- The small VOLEs' inputs read the replacement rows at the opened seeds and the VOLE blocks. -/
theorem usR_final (E : Cipher) {R R' : Fin nN → Blk → Blk} (s s' : Blk)
    (hs : ∀ k, restr p iv delta R (.inr (.inl k)) = restr p iv delta R' (.inr (.inl k)))
    (hv : ∀ ij, restr p iv delta R (.inr (.inr (.inl ij))) =
      restr p iv delta R' (.inr (.inr (.inl ij)))) :
    usR p iv (rowAt (xIn iv) nN (hidSet delta) E R s) =
      usR p iv (rowAt (xIn iv) nN (hidSet delta) E R' s') := by
  unfold usR
  refine Array.map_congr_left fun i hi => ?_
  have hi := Array.mem_range.1 hi
  refine congrArg bytesOfWords ?_
  unfold smallR
  refine List.foldl_ext _ _ _ fun acc j hj => ?_
  have hj := List.mem_range.1 hj
  by_cases hjd : j = BAVC.deltaIndex delta i
  · subst hjd
    have hm : hLeaf delta i ∈ hidSet delta := hLeaf_mem delta ⟨i, hi⟩
    dsimp only
    rw [show BAVC.treePos i (BAVC.deltaIndex delta i) = hLeaf delta i from rfl,
      rowAt_hid E R s hm, rowAt_hid E R' s' hm]
    refine congrArg (xorWords acc) (congrArg wordsOf (prgR_congr fun j' hj' => ?_))
    have := hv (⟨i, hi⟩, ⟨j', hj'⟩)
    simp only [restr, pts] at this
    exact this
  · dsimp only
    rw [rows_off E s s' hs _ (treePos_lt hi hj) (treePos_not_mem delta hi hj hjd)]

/-- **The fully punctured hidden part reads the replacement rows only at the points.** -/
theorem hidOfRows_final (E : Cipher) {R R' : Fin nN → Blk → Blk} (s s' : Blk)
    (h : restr p iv delta R = restr p iv delta R') :
    hidOfRows p iv delta (rowAt (xIn iv) nN (hidSet delta) E R s) =
      hidOfRows p iv delta (rowAt (xIn iv) nN (hidSet delta) E R' s') := by
  have hR := fun a => congrFun h a
  have h3 := usR_final E s s' (fun k => hR _) (fun ij => hR _)
  have h4 : prgR (rowAt (xIn iv) nN (hidSet delta) E R s 0) iv (((1 : UInt32) <<< 31) - 1) 0
      ((8 * p.nMask + 127) / 128) = prgR (rowAt (xIn iv) nN (hidSet delta) E R' s' 0) iv
      (((1 : UInt32) <<< 31) - 1) 0 ((8 * p.nMask + 127) / 128) := by
    rw [rowAt_hid E R s (root_mem delta), rowAt_hid E R' s' (root_mem delta)]
    exact prgR_congr fun j hj => hR (.inr (.inr (.inr ⟨j, hj⟩)))
  unfold hidOfRows
  rw [h3, h4]
  refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun k => ?_) rfl)
  · simp only
    rw [rowAt_hid E R s (hLeaf_mem delta i), rowAt_hid E R' s' (hLeaf_mem delta i)]
    exact congrArg (blk 32) (prgR_congr fun b hb => hR (.inl (i, ⟨b, hb⟩)))
  · simp only
    split_ifs with hk
    · rw [rowAt_hid E R s (oPar_mem delta ⟨k, hk⟩), rowAt_hid E R' s' (oPar_mem delta ⟨k, hk⟩)]
      exact hR (.inr (.inl ⟨k, hk⟩))
    · rfl

/-! ## The fully punctured hidden part from the values at the points -/

variable (p iv delta)

/-- The commitments from their blocks. -/
def comsF (a1 : Fin BAVC.tau × Fin 2 → Blk) : Fin BAVC.tau → Bytes 32 :=
  fun i => blk 32 (ba (a1 (i, 0)) ++ ba (a1 (i, 1)))

/-- The opened seeds from their values (zero past `openCount Δ`). -/
def seedsF (a2 : Fin (openCount delta) → Blk) : Fin 105 → Blk :=
  fun k => if h : k.val < openCount delta then a2 ⟨k, h⟩ else fun _ => 0

lemma hi_div_lt {t : ℕ} (ht : t < p.nMask) : t / 16 < nHi p := by
  simp only [nHi]; omega

/-- `u_hi` from the root's blocks: their first `n_mask` bytes. -/
def hiF (a4 : Fin (nHi p) → Blk) : Bytes p.nMask :=
  fun t => a4 ⟨t / 16, hi_div_lt p t.isLt⟩ ⟨t % 16, Nat.mod_lt _ (by norm_num)⟩

/-- The pads without `u_hi` and the sibling answers. -/
abbrev P5 := Bytes p.witnessBytes × Bytes (labelBytes p) ×
  (Fin (BAVC.tau - 1) → Bytes p.correctionBytes) × (Fin BAVC.tau → Bytes p.nMask) ×
  (Fin BAVC.tau → Bytes (restBytes p))

/-- The pads' layout of the columns `us` (as `padsOfArrays`). -/
def first5 (us : Array ByteArray) : P5 p :=
  (blk p.witnessBytes us[0]!, blk (labelBytes p) (us[0]!.extract p.witnessBytes p.correctionBytes),
    fun i => blk p.correctionBytes us[i.val + 1]!,
    fun i => blk p.nMask (us[i.val]!.extract p.correctionBytes (p.correctionBytes + p.nMask)),
    fun i => blk (restBytes p) (us[i.val]!.extract (p.correctionBytes + p.nMask) p.colBytes))

/-- The pads from the five column parts and `u_hi`. -/
def asm (f : P5 p) (h : Bytes p.nMask) : PadsU p := (f.1, f.2.1, f.2.2.1, f.2.2.2.1, f.2.2.2.2, h)

/-- `asm` as a bijection. -/
def asmEquiv : P5 p × Bytes p.nMask ≃ PadsU p where
  toFun z := asm p z.1 z.2
  invFun u := ((u.1, u.2.1, u.2.2.1, u.2.2.2.1, u.2.2.2.2.1), u.2.2.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

lemma dropSib_pads (us : Array ByteArray) (hi : ByteArray) :
    dropSib (padsOfArrays p us hi #[]) = asm p (first5 p us) (blk p.nMask hi) := rfl

/-- The fully punctured hidden part as a function of the values at the points. -/
noncomputable def finalF (E : Cipher) (x : Parts p delta) : Hidden p :=
  hidOfRows p iv delta (rowAt (xIn iv) nN (hidSet delta) E (rowsOf p iv delta ((partsEquiv p delta).symm x)) 0)

/-- The column parts: they depend on the opened seeds and the VOLE blocks only. -/
noncomputable def p5F (E : Cipher) (a2 : Fin (openCount delta) → Blk)
    (a3 : Fin BAVC.tau × Fin p.voleColBlocks → Blk) : P5 p :=
  first5 p (usR p iv (rowAt (xIn iv) nN (hidSet delta) E
    (rowsOf p iv delta ((partsEquiv p delta).symm (fun _ => 0, a2, a3, fun _ => 0))) 0))

lemma prgR_two (r : Blk → Blk) (iv : ByteArray) (t c : UInt32) :
    prgR r iv t c 2 = ba (r (blk 16 (AES.ctrBlock iv (c + (0 : ℕ).toUInt32) t))) ++
      ba (r (blk 16 (AES.ctrBlock iv (c + (1 : ℕ).toUInt32) t))) := by
  simp only [prgR, show List.range 2 = [0, 1] from rfl, List.foldl_cons, List.foldl_nil,
    ByteArray.empty_append]

/-- **The fully punctured hidden part, part by part.** -/
theorem finalF_eq (hp : SmallParams p) (E : Cipher) (x : Parts p delta) :
    finalF p iv delta E x = (comsF x.1, seedsF delta x.2.1,
      asm p (p5F p iv delta E x.2.1 x.2.2.1) (hiF p x.2.2.2)) := by
  set a := (partsEquiv p delta).symm x
  have hpt := rowsOf_pts p iv delta hp a
  have hus : usR p iv (rowAt (xIn iv) nN (hidSet delta) E (rowsOf p iv delta a) 0) =
      usR p iv (rowAt (xIn iv) nN (hidSet delta) E
        (rowsOf p iv delta ((partsEquiv p delta).symm (fun _ => 0, x.2.1, x.2.2.1, fun _ => 0))) 0) :=
    usR_final E 0 0 (fun k => by rw [restr_rowsOf p iv delta hp, restr_rowsOf p iv delta hp]; rfl)
      (fun ij => by rw [restr_rowsOf p iv delta hp, restr_rowsOf p iv delta hp]; rfl)
  have hhi : blk p.nMask (prgR (rowAt (xIn iv) nN (hidSet delta) E (rowsOf p iv delta a) 0 0) iv
      (((1 : UInt32) <<< 31) - 1) 0 ((8 * p.nMask + 127) / 128)) = hiF p x.2.2.2 := by
    funext t
    rw [get_blk, rowAt_hid E _ 0 (root_mem delta), prgR_get _ _ _ _ (by simp only [nHi] at *; omega)]
    have := hpt (.inr (.inr (.inr ⟨t / 16, hi_div_lt p t.isLt⟩)))
    simp only [pts, hiPt] at this
    rw [this]
    rfl
  unfold finalF hidOfRows
  rw [dropSib_pads, hus, hhi]
  refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun k => ?_) rfl)
  · simp only
    rw [rowAt_hid E _ 0 (hLeaf_mem delta i), prgR_two]
    have h0 : rowsOf p iv delta ((partsEquiv p delta).symm x) ⟨hLeaf delta i, hLeaf_lt delta i.isLt⟩
        (blk 16 (AES.ctrBlock iv (0 + Nat.toUInt32 0) (i.val + BAVC.numLeaves - 1).toUInt32)) =
        x.1 (i, 0) := hpt (.inl (i, 0))
    have h1 : rowsOf p iv delta ((partsEquiv p delta).symm x) ⟨hLeaf delta i, hLeaf_lt delta i.isLt⟩
        (blk 16 (AES.ctrBlock iv (0 + Nat.toUInt32 1) (i.val + BAVC.numLeaves - 1).toUInt32)) =
        x.1 (i, 1) := hpt (.inl (i, 1))
    rw [h0, h1]
    rfl
  · simp only [seedsF]
    split_ifs with hk
    · rw [rowAt_hid E _ 0 (oPar_mem delta ⟨k, hk⟩)]
      exact hpt (.inr (.inl ⟨k, hk⟩))
    · rfl

/-! ## Each part is uniform -/

/-- An injective map between types of the same size pushes uniform to uniform. -/
lemma close_of_inj {α β : Type*} [Fintype α] [Fintype β] (f : α → β) (hf : Function.Injective f)
    (hc : Fintype.card α = Fintype.card β) : Close 0 f (id : β → β) := by
  let e := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2 ⟨hf, hc⟩)
  exact (close_equiv e id).congr (fun _ => rfl) fun _ => rfl

lemma get!_ba_append {u v : Blk} {t : ℕ} :
    (ba u ++ ba v).get! t = if t < 16 then (ba u).get! t else (ba v).get! (t - 16) := by
  rw [get!_append, size_ba]

/-- **The commitments are uniform.** -/
theorem comsF_close : Close 0 comsF (id : (Fin BAVC.tau → Bytes 32) → _) := by
  refine close_of_inj _ (fun a a' h => funext fun ib => funext fun t => ?_) ?_
  · obtain ⟨i, b⟩ := ib
    have hi := congrFun h i
    simp only [comsF] at hi
    rcases Fin.exists_fin_two.1 ⟨b, rfl⟩ with rfl | rfl
    · have := congrFun hi ⟨t, by omega⟩
      simp only [get_blk, get!_ba_append, t.isLt, ↓reduceIte, get!_ba _ t.isLt] at this
      exact this
    · have := congrFun hi ⟨t + 16, by omega⟩
      simp only [get_blk, get!_ba_append, show ¬ t.val + 16 < 16 by omega, ↓reduceIte,
        Nat.add_sub_cancel, get!_ba _ t.isLt] at this
      exact this
  · simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Prob.card_uint8, ← pow_mul]
    rw [show 8 * 16 * (BAVC.tau * 2) = 8 * 32 * BAVC.tau by ring]

/-- The seed slots `k < openCount Δ`. -/
abbrev SeedSlot := {k : Fin 105 // k.val < openCount delta}

/-- Seeds on the slots, zero elsewhere. -/
def embSeeds (v : SeedSlot delta → Blk) : Fin 105 → Blk :=
  fun k => if h : k.val < openCount delta then v ⟨k, h⟩ else fun _ => 0

/-- **The opened seeds have the law of the ideal (zero-tailed) seeds.** -/
theorem seedsF_close : Close 0 (seedsF delta) (zeroTail delta) := by
  have h1 := close_restrict (K := Fin (openCount delta)) (R := Blk)
    (x := fun j : SeedSlot delta => (⟨j.1.val, j.2⟩ : Fin (openCount delta)))
    (fun j j' e => Subtype.ext (Fin.ext (by simpa using congrArg Fin.val e)))
  have h2 := close_restrict (K := Fin 105) (R := Blk) (x := fun j : SeedSlot delta => j.1)
    Subtype.val_injective
  refine ((h1.map (embSeeds delta)).trans (h2.map (embSeeds delta)).symm).mono (by norm_num)
    |>.congr (fun a2 => ?_) fun sd => ?_
  · funext k; simp only [embSeeds, seedsF, Function.comp_apply]
  · funext k; simp only [embSeeds, zeroTail, Function.comp_apply]; split_ifs <;> rfl

/-- The byte positions of `u_hi` in the root's blocks. -/
def hiPos (t : Fin p.nMask) : Fin (nHi p) × Fin 16 :=
  (⟨t / 16, hi_div_lt p t.isLt⟩, ⟨t % 16, Nat.mod_lt _ (by norm_num)⟩)

/-- **`u_hi` is uniform.** -/
theorem hiF_close : Close 0 (hiF p) (id : Bytes p.nMask → _) := by
  have hinj : Function.Injective (hiPos p) := fun t t' e => by
    simp only [hiPos, Prod.mk.injEq, Fin.mk.injEq] at e
    exact Fin.ext (by have := Nat.div_add_mod t.val 16; have := Nat.div_add_mod t'.val 16; omega)
  have h1 := close_restrict (K := Fin (nHi p) × Fin 16) (R := UInt8) hinj
  have h2 := close_equiv (Equiv.curry (Fin (nHi p)) (Fin 16) UInt8).symm
    (fun g : Fin (nHi p) × Fin 16 → UInt8 => g ∘ hiPos p)
  exact ((h2.trans h1).mono (by norm_num)).congr (fun _ => rfl) fun _ => rfl

/-! ## The column parts are a bijection of the VOLE blocks -/

lemma smallR_size (i : ℕ) (rows : ℕ → Blk → Blk) : (smallR p iv i rows).size = p.colBytes / 8 := by
  unfold smallR
  have : ∀ (l : List ℕ) (acc : Array UInt64), (l.foldl (fun acc j => xorWords acc
      (wordsOf (prgR (rows j) iv (((1 : UInt32) <<< 31) + i.toUInt32) 0 p.voleColBlocks))) acc).size =
      acc.size := by
    intro l; induction l with
    | nil => intro _; rfl
    | cons j l ih => intro acc; rw [List.foldl_cons, ih, xorWords_size]
  rw [this, zeroCol, Array.size_replicate]

lemma usR_get (ρ : ℕ → Blk → Blk) {i : ℕ} (hi : i < BAVC.tau) :
    (usR p iv ρ)[i]! = bytesOfWords (smallR p iv i fun j => ρ (BAVC.treePos i j)) :=
  getElem!_range_map _ _ hi

lemma usR_get_size (ρ : ℕ → Blk → Blk) {i : ℕ} (hi : i < BAVC.tau) :
    ((usR p iv ρ)[i]!).size = p.colBytes := by
  rw [usR_get p iv ρ hi, bytesOfWords_size, smallR_size]
  have := colBytes_mod8 p; omega

/-- The column parts determine the columns. -/
theorem first5_cols {us us' : Array ByteArray} (hs : ∀ i < BAVC.tau, (us[i]!).size = p.colBytes)
    (hs' : ∀ i < BAVC.tau, (us'[i]!).size = p.colBytes) (h : first5 p us = first5 p us') :
    ∀ i < BAVC.tau, us[i]! = us'[i]! := by
  have key : ∀ us : Array ByteArray, (∀ i < BAVC.tau, (us[i]!).size = p.colBytes) →
      ∀ i < BAVC.tau, usBytes p ((first5 p us).1, (first5 p us).2.1, (first5 p us).2.2.1,
        (first5 p us).2.2.2.1, (first5 p us).2.2.2.2, fun _ => 0, fun _ _ => 0) i = us[i]! := by
    intro us hs i hi
    let X : ℕ → ByteArray := fun j => if j < BAVC.tau then us[j]! else Prover.zeros p.colBytes
    have hX : ∀ j, (X j).size = p.colBytes := fun j => by
      simp only [X]; split_ifs with hj
      · exact hs j hj
      · exact zeros_size _
    have e := usBytes_reassemble p X hX (fun _ => 0) (fun _ _ => 0) hi
    have h1 : ∀ j : Fin (BAVC.tau - 1), j.val + 1 < BAVC.tau := fun j => by have := j.isLt; omega
    have h2 : ∀ j : Fin BAVC.tau, j.val < BAVC.tau := fun j => j.isLt
    simp only [X, show (0 : ℕ) < BAVC.tau from by decide, h1, h2, hi, ite_true] at e
    exact e
  intro i hi
  rw [← key us hs i hi, ← key us' hs' i hi, h]

lemma prgR_get' (r : Blk → Blk) (tw c : UInt32) {n j : ℕ} (hj : j < n) (t : Fin 16) :
    (prgR r iv tw c n).get! (16 * j + t) = r (blk 16 (AES.ctrBlock iv (c + j.toUInt32) tw)) t := by
  rw [prgR_get _ _ _ _ (by omega)]
  have e1 : (16 * j + t.val) / 16 = j := by omega
  have e2 : (⟨(16 * j + t.val) % 16, Nat.mod_lt _ (by norm_num)⟩ : Fin 16) = t := Fin.ext (by simp)
  rw [e2, e1]

/-- **For fixed opened seeds, the column parts are a bijection of the VOLE blocks**: every column
`u^{(i)}` is the opened leaves' part XOR the hidden leaf's VOLE blocks. -/
theorem p5F_injective (hp : SmallParams p) (E : Cipher) (a2 : Fin (openCount delta) → Blk) :
    Function.Injective (p5F p iv delta E a2) := by
  intro a3 a3' h
  set R := rowsOf p iv delta ((partsEquiv p delta).symm (fun _ => 0, a2, a3, fun _ => 0))
  set R' := rowsOf p iv delta ((partsEquiv p delta).symm (fun _ => 0, a2, a3', fun _ => 0))
  set ρ := rowAt (xIn iv) nN (hidSet delta) E R 0
  set ρ' := rowAt (xIn iv) nN (hidSet delta) E R' 0
  have hcols := first5_cols p (fun i hi => usR_get_size p iv ρ hi)
    (fun i hi => usR_get_size p iv ρ' hi) h
  have hseed : ∀ k, restr p iv delta R (.inr (.inl k)) = restr p iv delta R' (.inr (.inl k)) :=
    fun k => by rw [restr_rowsOf p iv delta hp, restr_rowsOf p iv delta hp]; rfl
  have hoff : ∀ m < nN, m ∉ hidSet delta → ρ m = ρ' m := rows_off E 0 0 hseed
  funext ij
  funext t
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := ij
  have hhl : ρ (hLeaf delta i) = R ⟨hLeaf delta i, hLeaf_lt delta hi⟩ :=
    rowAt_hid E R 0 (hLeaf_mem delta ⟨i, hi⟩)
  have hhl' : ρ' (hLeaf delta i) = R' ⟨hLeaf delta i, hLeaf_lt delta hi⟩ :=
    rowAt_hid E R' 0 (hLeaf_mem delta ⟨i, hi⟩)
  have hc := hcols i hi
  rw [usR_get p iv ρ hi, usR_get p iv ρ' hi] at hc
  unfold smallR at hc
  have hsz : ∀ (r : Blk → Blk), (wordsOf (prgR r iv (((1 : UInt32) <<< 31) + i.toUInt32) 0
      p.voleColBlocks)).size = p.colBytes / 8 := fun r => by
    simp only [wordsOf, Array.size_map, Array.size_range, prgR_size, Params.colBytes]
  have hk : 16 * j + t.val < 8 * (p.colBytes / 8) := by
    simp only [Params.colBytes]; omega
  have hd := fold_xor_diff (fun j => wordsOf (prgR (ρ (BAVC.treePos i j)) iv
      (((1 : UInt32) <<< 31) + i.toUInt32) 0 p.voleColBlocks))
    (fun j => wordsOf (prgR (ρ' (BAVC.treePos i j)) iv
      (((1 : UInt32) <<< 31) + i.toUInt32) 0 p.voleColBlocks))
    (p.colBytes / 8) (BAVC.deltaIndex delta i) hk (List.range (2 ^ BAVC.kOf i)) List.nodup_range
    (fun _ _ => hsz _) (fun _ _ => hsz _) (fun j' hj' hjd => by
      rw [hoff _ (treePos_lt hi (List.mem_range.1 hj'))
        (treePos_not_mem delta hi (List.mem_range.1 hj') hjd)])
    (zeroCol p) (zeroCol p) (by simp [zeroCol]) (by simp [zeroCol])
  rw [hc, UInt8.xor_self, UInt8.xor_self, UInt8.zero_xor] at hd
  simp only [show BAVC.deltaIndex delta i ∈ List.range (2 ^ BAVC.kOf i) from
    List.mem_range.2 (deltaIndex_lt delta i), ↓reduceIte] at hd
  rw [eq_comm, UInt8.xor_eq_zero_iff] at hd
  have h8 : ∀ r : Blk → Blk, (prgR r iv (((1 : UInt32) <<< 31) + i.toUInt32) 0
      p.voleColBlocks).size % 8 = 0 := fun r => by rw [prgR_size]; omega
  simp only [bytesOfWords_wordsOf (h8 _)] at hd
  rw [show BAVC.treePos i (BAVC.deltaIndex delta i) = hLeaf delta i from rfl, hhl, hhl',
    prgR_get' iv _ _ _ hj t, prgR_get' iv _ _ _ hj t] at hd
  have e : R ⟨hLeaf delta i, hLeaf_lt delta hi⟩ (blk 16 (AES.ctrBlock iv (0 + j.toUInt32)
      (((1 : UInt32) <<< 31) + i.toUInt32))) = a3 (⟨i, hi⟩, ⟨j, hj⟩) :=
    rowsOf_pts p iv delta hp _ (.inr (.inr (.inl (⟨i, hi⟩, ⟨j, hj⟩))))
  have e' : R' ⟨hLeaf delta i, hLeaf_lt delta hi⟩ (blk 16 (AES.ctrBlock iv (0 + j.toUInt32)
      (((1 : UInt32) <<< 31) + i.toUInt32))) = a3' (⟨i, hi⟩, ⟨j, hj⟩) :=
    rowsOf_pts p iv delta hp _ (.inr (.inr (.inl (⟨i, hi⟩, ⟨j, hj⟩))))
  rw [e, e'] at hd
  exact hd

theorem p5F_card :
    Fintype.card (Fin BAVC.tau × Fin p.voleColBlocks → Blk) = Fintype.card (P5 p) := by
  have h1 := labelBytes_add p
  have h2 := cb_add_nMask_le p
  simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Prob.card_uint8, ← pow_mul,
    ← pow_add]
  congr 1
  simp only [restBytes, Params.colBytes, BAVC.tau] at *
  omega

theorem p5F_close (hp : SmallParams p) (E : Cipher) (a2 : Fin (openCount delta) → Blk) :
    Close 0 (p5F p iv delta E a2) (id : P5 p → P5 p) :=
  close_of_inj _ (p5F_injective p iv delta hp E a2) (p5F_card p)

/-! ## The fully punctured experiment is the ideal one -/

/-- For fixed opened seeds, the pads are uniform. -/
theorem pads_close (hp : SmallParams p) (E : Cipher) (a2 : Fin (openCount delta) → Blk) :
    Close 0 (fun y : (Fin BAVC.tau × Fin p.voleColBlocks → Blk) × (Fin (nHi p) → Blk) =>
      asm p (p5F p iv delta E a2 y.1) (hiF p y.2)) (id : PadsU p → PadsU p) := by
  have h1 := (p5F_close p iv delta hp E a2).prod (hiF_close p)
  have h2 := h1.map fun z => asm p z.1 z.2
  have h3 : Close 0 (fun z : P5 p × Bytes p.nMask => asm p z.1 z.2) (id : PadsU p → PadsU p) :=
    close_equiv (asmEquiv p) id
  have h2' : Close 0 (fun y : (Fin BAVC.tau × Fin p.voleColBlocks → Blk) × (Fin (nHi p) → Blk) =>
      asm p (p5F p iv delta E a2 y.1) (hiF p y.2)) (fun z : P5 p × Bytes p.nMask => asm p z.1 z.2) :=
    fun D => (h2 D).trans (le_of_eq (by norm_num))
  exact fun D => ((h2'.trans h3) D).trans (le_of_eq (by norm_num))

/-- **For every cipher table, the fully punctured hidden part is exactly the ideal one.** -/
theorem final_close (hp : SmallParams p) (E : Cipher) :
    Close 0 (finalF p iv delta E) (hiddenIdeal (p := p) delta) := by
  have hB : Close 0 (fun y : (Fin (openCount delta) → Blk) ×
      ((Fin BAVC.tau × Fin p.voleColBlocks → Blk) × (Fin (nHi p) → Blk)) =>
        (seedsF delta y.1, asm p (p5F p iv delta E y.1 y.2.1) (hiF p y.2.2)))
      (fun z : (Fin (openCount delta) → Blk) × PadsU p => (seedsF delta z.1, z.2)) :=
    fun D => abs_pr_prod_sub_le
      (fun y : (Fin (openCount delta) → Blk) ×
        ((Fin BAVC.tau × Fin p.voleColBlocks → Blk) × (Fin (nHi p) → Blk)) =>
          D (seedsF delta y.1, asm p (p5F p iv delta E y.1 y.2.1) (hiF p y.2.2)))
      (fun z : (Fin (openCount delta) → Blk) × PadsU p => D (seedsF delta z.1, z.2))
      fun a2 => pads_close p iv delta hp E a2 fun u => D (seedsF delta a2, u)
  have hC : Close 0 (fun z : (Fin (openCount delta) → Blk) × PadsU p => (seedsF delta z.1, z.2))
      (fun z : (Fin 105 → Blk) × PadsU p => (zeroTail delta z.1, z.2)) := fun D =>
    (((seedsF_close delta).prod (close_self le_rfl (id : PadsU p → PadsU p))) D).trans
      (le_of_eq (by norm_num))
  have hBC : Close 0 (fun y : (Fin (openCount delta) → Blk) ×
      ((Fin BAVC.tau × Fin p.voleColBlocks → Blk) × (Fin (nHi p) → Blk)) =>
        (seedsF delta y.1, asm p (p5F p iv delta E y.1 y.2.1) (hiF p y.2.2)))
      (fun z : (Fin 105 → Blk) × PadsU p => (zeroTail delta z.1, z.2)) := fun D =>
    ((hB.trans hC) D).trans (le_of_eq (by norm_num))
  have hD := comsF_close.prod hBC
  intro D
  have e : (fun x => D (finalF p iv delta E x)) = fun x : Parts p delta =>
      D (comsF x.1, seedsF delta x.2.1, asm p (p5F p iv delta E x.2.1 x.2.2.1) (hiF p x.2.2.2)) :=
    funext fun x => by rw [finalF_eq p iv delta hp]
  rw [e]
  exact (hD D).trans (le_of_eq (by norm_num))

/-- The hidden part of the fully punctured experiment, from the coins, is `finalF` of the values
at the points. -/
lemma hidOfRows_eq_finalF (hp : SmallParams p) (E : Cipher) (R : Fin nN → Blk → Blk) (s : Blk) :
    hidOfRows p iv delta (rowAt (xIn iv) nN (hidSet delta) E R s) =
      finalF p iv delta E (partsEquiv p delta (restr p iv delta R)) := by
  unfold finalF
  refine hidOfRows_final E s 0 ?_
  rw [Equiv.symm_apply_apply, restr_rowsOf p iv delta hp]

/-- **The fully punctured experiment is the ideal one**: its distinguisher's success probability is
that of the ideal hidden part with an independent uniform table. -/
theorem exper_final (hp : SmallParams p) (A : Hidden p → Cipher → Prop) :
    exper (xIn iv) nN (hidSet delta) (hidOfRows p iv delta) A =
      idealPr (hiddenIdeal (p := p) delta) A := by
  refine exper_eq_of_close _ _ _ (fun E => ?_) A
  have h1 : Close 0 (fun R : Fin nN → Blk → Blk => finalF p iv delta E
      (partsEquiv p delta (restr p iv delta R))) (finalF p iv delta E) :=
    (((restr_close p iv delta hp).map fun a => finalF p iv delta E (partsEquiv p delta a)).trans
      (close_equiv (partsEquiv p delta) (finalF p iv delta E))).mono (by norm_num)
  have h2 := (close_prod_snd (α := Blk) (X := fun R : Fin nN → Blk → Blk =>
    finalF p iv delta E (partsEquiv p delta (restr p iv delta R)))).trans h1
  have h3 := h2.trans (final_close p iv delta hp E)
  have h4 : Close 0 (fun x : Blk × (Fin nN → Blk → Blk) =>
      finalF p iv delta E (partsEquiv p delta (restr p iv delta x.2))) (hiddenIdeal (p := p) delta) :=
    fun D => (h3 D).trans (le_of_eq (by norm_num))
  have hfun : (fun c : Coins Blk Blk nN =>
      hidOfRows p iv delta (rowAt (xIn iv) nN (hidSet delta) E c.2 c.1)) =
      fun x : Blk × (Fin nN → Blk → Blk) =>
        finalF p iv delta E (partsEquiv p delta (restr p iv delta x.2)) :=
    funext fun c => hidOfRows_eq_finalF p iv delta hp E c.2 c.1
  rw [hfun]
  exact h4

/-! ## Hop H4 in the ideal-cipher model -/

/-- **H4 in the ideal-cipher model, against a distinguisher that reads the cipher table**: with the
BAVC's cipher a uniform table `E` (`hiddenOutE`; with AES it is the executable commitment,
`hiddenOut_eq`), if `A` reads the table at most at `q` keys (whole rows; `hQ`, `hq`), its advantage
between the hidden part of a commitment from a uniform root seed (`realPr`) and the ideal hidden
part `hiddenIdeal` with an independent table (`idealPr`) is at most
`221 · (4607 + q) / 2¹²⁸`, for every `iv` and `Δ`. Here `221 = τ · 13` bounds the nodes on the
hidden paths (`hidSet_card`) and `4607 = 2L − 1` the other keys the commitment reads. The rows are
uniform functions (the PRF view of the ideal cipher); with uniform permutations, the switching
term of the hidden paths' rows is not included. -/
theorem hide_rom_query (hp : SmallParams p) (A : Hidden p → Cipher → Prop)
    (Q : Hidden p → Cipher → Finset Blk)
    (hQ : ∀ o G G', (∀ k ∈ Q o G, G k = G' k) → (A o G ↔ A o G')) {q : ℕ}
    (hq : ∀ o G, (Q o G).card ≤ q) :
    |realPr (fun seed E => hiddenOutE E p iv delta seed) A - idealPr (hiddenIdeal (p := p) delta) A| ≤
      221 * (4607 + q) / 2 ^ 128 := by
  have h := hide_puncture p iv delta A Q hQ hq
  rw [exper_empty, exper_final p iv delta hp A] at h
  refine h.trans ?_
  have hc : ((hidSet delta).card : ℝ) ≤ 221 := by exact_mod_cast hidSet_card delta
  have hn : ((nN + q : ℕ) : ℝ) = 4607 + q := by push_cast; rfl
  rw [mul_div_assoc, hn]
  exact mul_le_mul_of_nonneg_right hc (by positivity)

/-- **The H4 hypothesis in the ideal-cipher model** (`HideHyp` with the cipher a uniform table,
averaged over the table): for every `iv` and `Δ`, the hidden part of a commitment from a uniform root
seed is `ε`-close to the ideal hidden part. -/
def HideHypIC (p : Params) (ε : ℝ) : Prop :=
  ∀ iv delta : ByteArray, Close ε (fun x : Blk × Cipher => hiddenOutE x.2 p iv delta x.1)
    (fun x : Hidden p × Cipher => hiddenIdeal (p := p) delta x.1)

/-- **`HideHypIC` holds with `ε_bavc = 221 · 4607 / 2¹²⁸ < 2⁻¹¹⁸`.** -/
theorem hideHypIC_holds (hp : SmallParams p) : HideHypIC p (221 * 4607 / 2 ^ 128) := by
  intro iv delta D
  have h := hide_rom_query p iv delta hp (fun o _ => D o) (fun _ _ => ∅) (fun _ _ _ _ => Iff.rfl)
    (q := 0) (fun _ _ => by simp)
  unfold realPr idealPr at h
  norm_num at h ⊢
  convert h using 3

end VoleMole.ZK.Sim
