import VoleMole.ZK.HopsROM
import VoleMole.ZK.IdealCipher

/-!
# The BAVC commitment with the cipher as a parameter (hop H4, ideal-cipher model)

The executable BAVC (`Verifier/BAVC.lean`) calls its CTR PRG through `HasPrg` (`Verifier/Prg.lean`;
AES-128, `AES.prg`, for the executable code). For the ideal-cipher version of `HideHyp` the hidden
part of a commitment (`Sim.hiddenOut`) is rebuilt here, proof-only, from a cipher table
`E : Bytes 16 → Bytes 16 → Bytes 16` (key ↦ row):

* `prgR r iv t c n`: the CTR PRG with the row `r` (block `j` is `r` at `ctrBlock iv (c + j) t`);
  `prg_eq_prgR`: `AES.prg` is `prgR` with the row of `aesTable` (AES-128 as a table);
* **`icPrg E`**: the `HasPrg` instance of the table `E` (`prgR` of `E`'s row at a 16-byte key,
  `icPrg_prg`); with it the whole executable prover and verifier run with the ideal cipher, and
  `icPrg aesTable` is the executable instance (`icPrg_aes`);
* `xIn iv`: the input of GGM node `c ≥ 1` under its parent's key (`ctrBlock iv (c − 1) % 2`, tweak
  the parent's index), the inputs of `IC.rowAt`; the tree's node values are `IC.keyAt`
  (`keyAt_rows`: for a PRG that is `prgR` of the table's rows, the executable tree
  `Bridge.treeNode`; `keyAt_aes`, `keyAt_ic`);
* `hidOfRows`: the hidden part as a function of the nodes' rows (the hidden leaves' commitments,
  the opened seeds, all small VOLEs' inputs `u^{(i)}`, the root's `u_hi`), and
  `hiddenOutE E = hidOfRows ∘ IC.rowAt ∅ E` the cipher-parametric hidden part;
* **`hiddenOut_rows`**: `Sim.hiddenOut p iv Δ seed = hiddenOutE E p iv Δ seed` for such a PRG (by
  unfolding the executable folds: `Bridge.expandTree_get`, `Bridge.leavesOf_eq`,
  `BavcLemmas.openSeeds_eq`): `hiddenOut_eq` (AES), `hiddenOut_ic` (`icPrg E`).

The side conditions of the GGM hybrid `IC.puncture` for the hidden paths `Bridge.hid Δ`:
`xIn_sib` (siblings have different inputs: `Bridge.ctrBlock_inj`), `hidOfRows_point` (the hidden
part never reads a hidden node's value, only its row: the opened seeds are siblings, and `u_hi`
uses the mask tweak, `Bridge.ctrBlock_ne_of_roles`), `hidOfRows_congr` (it reads nodes below
`2L − 1` only).
-/

open Finset

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.Privacy VoleMole.ZK.IC

/-- A 16-byte block. -/
abbrev Blk := Bytes 16

/-- A block cipher as a table: for every key, a row (block ↦ block). -/
abbrev Cipher := Blk → Blk → Blk

/-- **AES-128 as a table.** -/
def aesTable : Cipher := fun k z => blk 16 (AES.encrypt (AES.expandKey (ba k)) (ba z))

/-! ## The CTR PRG with a row -/

/-- The CTR PRG with the row `r`: `n` blocks, block `j` being `r` at `ctrBlock iv (c + j) t`. -/
def prgR (r : Blk → Blk) (iv : ByteArray) (t c : UInt32) (n : ℕ) : ByteArray :=
  (List.range n).foldl (fun out j => out ++ ba (r (blk 16 (AES.ctrBlock iv (c + j.toUInt32) t))))
    ByteArray.empty

lemma ctrBlock_size (iv : ByteArray) (c t : UInt32) : (AES.ctrBlock iv c t).size = 16 := by
  simp only [AES.ctrBlock, size_pushLE32, ByteArray.size_empty]

lemma prgR_eq_map (r : Blk → Blk) (iv : ByteArray) (t c : UInt32) (n : ℕ) :
    prgR r iv t c n = ((List.range n).map fun j =>
      ba (r (blk 16 (AES.ctrBlock iv (c + j.toUInt32) t)))).foldl (· ++ ·) ByteArray.empty := by
  rw [prgR, List.foldl_map]

lemma prgR_size (r : Blk → Blk) (iv : ByteArray) (t c : UInt32) (n : ℕ) :
    (prgR r iv t c n).size = 16 * n := by
  rw [prgR_eq_map, size_foldl_uniform 16 _ _ (fun b hb => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hb; exact size_ba _)]
  simp

/-- Block `j` of `prgR`. -/
lemma prgR_block (r : Blk → Blk) (iv : ByteArray) (t c : UInt32) {n j : ℕ} (hj : j < n) :
    (prgR r iv t c n).extract (16 * j) (16 * j + 16) =
      ba (r (blk 16 (AES.ctrBlock iv (c + j.toUInt32) t))) := by
  rw [prgR_eq_map]
  have h := extract_foldl_uniform 16 ((List.range n).map fun j =>
      ba (r (blk 16 (AES.ctrBlock iv (c + j.toUInt32) t)))) ByteArray.empty (fun b hb => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hb; exact size_ba _) j (by simpa using hj)
  simp only [ByteArray.size_empty, Nat.zero_add] at h
  rw [h]
  simp

/-- `prgR` reads its row only at the CTR blocks of its counters. -/
lemma prgR_congr {r r' : Blk → Blk} {iv : ByteArray} {t c : UInt32} {n : ℕ}
    (h : ∀ j < n, r (blk 16 (AES.ctrBlock iv (c + j.toUInt32) t)) =
      r' (blk 16 (AES.ctrBlock iv (c + j.toUInt32) t))) :
    prgR r iv t c n = prgR r' iv t c n := by
  unfold prgR
  exact List.foldl_ext _ _ _ fun acc j hj => by rw [h j (List.mem_range.1 hj)]

/-- **`AES.prg` is `prgR` with the row of `aesTable`.** -/
theorem prg_eq_prgR (k : Blk) (iv : ByteArray) (t c : UInt32) (n : ℕ) :
    AES.prg (ba k) iv t c n = prgR (aesTable k) iv t c n := by
  rw [AES.prg, prgExpanded_eq, prgR]
  refine List.foldl_ext _ _ _ fun acc j _ => ?_
  rw [aesTable, ba_blk_of_size (ctrBlock_size _ _ _), ba_blk_of_size (encrypt_size _ _)]

/-! ## The tree and the hidden part from the rows -/

/-- The number of nodes of the tree, `2L − 1`. -/
abbrev nN : ℕ := BAVC.numNodes

/-- **The input of GGM node `c ≥ 1`** under its parent's key: counter `(c − 1) % 2` (left or right
child), tweak the parent's index (`BAVC.children`). -/
def xIn (iv : ByteArray) (c : ℕ) : Blk :=
  blk 16 (AES.ctrBlock iv (0 + ((c - 1) % 2).toUInt32) ((c - 1) / 2).toUInt32)

/-- The hidden leaf of vector `i`. -/
def hLeaf (delta : ByteArray) (i : ℕ) : ℕ := BAVC.treePos i (BAVC.deltaIndex delta i)

/-- The `k`-th opened node. -/
def oNode (delta : ByteArray) (k : ℕ) : ℕ := (BAVC.openNodes delta)[k]!

/-- `u^{(i)} = Σ_j R_j` (`Prover.smallVoleUWords`) with leaf `j`'s row `rows j`. -/
def smallR (p : Params) (iv : ByteArray) (i : ℕ) (rows : ℕ → Blk → Blk) : Array UInt64 :=
  (List.range (2 ^ BAVC.kOf i)).foldl (fun acc j => xorWords acc
    (wordsOf (prgR (rows j) iv (((1 : UInt32) <<< 31) + i.toUInt32) 0 p.voleColBlocks))) (zeroCol p)

/-- The small VOLEs' inputs from the rows of the leaves. -/
def usR (p : Params) (iv : ByteArray) (ρ : ℕ → Blk → Blk) : Array ByteArray :=
  (Array.range BAVC.tau).map fun i => bytesOfWords (smallR p iv i fun j => ρ (BAVC.treePos i j))

/-- **The hidden part of a commitment from the nodes' rows** `ρ`: the hidden leaves' commitments
(their rows at the leaf tweak), the opened seeds (their parents' rows at their inputs), the small
VOLEs' inputs (the leaves' rows at the VOLE tweak) and `u_hi` (the root's row at the mask tweak). -/
def hidOfRows (p : Params) (iv delta : ByteArray) (ρ : ℕ → Blk → Blk) : Hidden p :=
  (fun i => blk 32 (prgR (ρ (hLeaf delta i)) iv (i.val + BAVC.numLeaves - 1).toUInt32 0 2),
   fun k => if k.val < openCount delta then ρ ((oNode delta k - 1) / 2) (xIn iv (oNode delta k))
     else fun _ => 0,
   dropSib (padsOfArrays p (usR p iv ρ)
     (prgR (ρ 0) iv (((1 : UInt32) <<< 31) - 1) 0 ((8 * p.nMask + 127) / 128)) #[]))

/-- **The hidden part with the cipher `E`**: `hidOfRows` of the real rows (nothing replaced). -/
def hiddenOutE (E : Cipher) (p : Params) (iv delta : ByteArray) (seed : Blk) : Hidden p :=
  hidOfRows p iv delta (rowAt (xIn iv) nN ∅ E (fun _ _ => seed) seed)

/-! ## The bridge to the executable commitment -/

lemma xIn_succ (iv : ByteArray) (m : ℕ) :
    xIn iv (m + 1) = blk 16 (AES.ctrBlock iv (0 + (m % 2).toUInt32) (m / 2).toUInt32) := by
  simp only [xIn, Nat.add_sub_cancel]

/-! ## The CTR PRG of a cipher table -/

/-- **The CTR PRG of the cipher table `E`**: on a 16-byte key `k`, `prgR` with `E`'s row at `k`
(block `j` is `E_k(ctrBlock iv (c + j) t)`). The protocol only uses 16-byte keys; a key of any
other length is answered by AES, so that the PRG of `aesTable` is `AES.prg` itself (`icPrg_aes`). -/
def icPrgF (E : Cipher) (key iv : ByteArray) (t c : UInt32) (n : ℕ) : ByteArray :=
  if key.size = 16 then prgR (E (blk 16 key)) iv t c n else AES.prg key iv t c n

/-- **The ideal-cipher PRG**: the `HasPrg` instance of the cipher table `E`. With it, the
executable BAVC, VOLE expansion, prover and verifier (all written against `HasPrg`) run with the
cipher `E` in place of AES. -/
@[reducible] def icPrg (E : Cipher) : HasPrg where
  prg := icPrgF E
  prg_size key iv t c n := by
    unfold icPrgF
    split_ifs
    · exact prgR_size _ _ _ _ _
    · exact AES.prg_size_aes _ _ _ _ _

/-- On a 16-byte key, the ideal-cipher PRG reads the table at that key only. -/
lemma icPrg_prg (E : Cipher) (k : Blk) (iv : ByteArray) (t c : UInt32) (n : ℕ) :
    @HasPrg.prg (icPrg E) (ba k) iv t c n = prgR (E k) iv t c n := by
  show icPrgF E (ba k) iv t c n = _
  simp only [icPrgF, size_ba, ↓reduceIte, blk_ba]

/-- **The ideal-cipher PRG of AES is the executable PRG**: `icPrg aesTable` is the instance
`aesPrg` of the executable code. -/
theorem icPrg_aes : icPrg aesTable = aesPrg := by
  have h : icPrgF aesTable = AES.prg := by
    funext key iv t c n
    unfold icPrgF
    split_ifs with hk
    · rw [← prg_eq_prgR, ba_blk_of_size hk]
    · rfl
  show HasPrg.mk (icPrgF aesTable) _ = HasPrg.mk AES.prg _
  congr

/-! ## The bridge to the executable commitment, for any PRG -/

section Generic

variable [HasPrg]

/-- **The nodes of `IC.keyAt` are the executable tree's**, for a PRG that is `prgR` of the table's
row at every 16-byte key (`hE`: AES with `aesTable`, `icPrg E` with `E`). -/
theorem keyAt_rows (E : Cipher)
    (hE : ∀ (k : Blk) (iv : ByteArray) (t c : UInt32) (n : ℕ),
      HasPrg.prg (ba k) iv t c n = prgR (E k) iv t c n)
    (iv : ByteArray) (R : Fin nN → Blk → Blk) (seed : Blk) :
    ∀ n, ba (keyAt (xIn iv) nN ∅ E R seed n) = treeNode (ba seed) iv n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | m
    · rw [keyAt_zero, treeNode]
    · have h := ih (m / 2) (by omega)
      show ba (rowAt (xIn iv) nN ∅ E R seed (m / 2) (xIn iv (m + 1))) = _
      rw [rowAt_of_not_mem (Finset.notMem_empty _), treeNode, BAVC.block, BAVC.children, ← h,
        hE, prgR_block _ _ _ _ (Nat.mod_lt _ (by norm_num)), xIn_succ]

lemma treeNode_size' (seed iv : ByteArray) (hs : seed.size = 16) (n : ℕ) :
    (treeNode seed iv n).size = 16 := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · rw [treeNode]; exact hs
  · exact treeNode_size _ _ h

omit [HasPrg] in
lemma hnone_eq (j : ℕ) : ((none : Option ℕ) == some j) = false := rfl

/-- The leaf keys of the executable commitment are the tree's leaves. -/
lemma leafKey_commit (seed iv : ByteArray) (hs : seed.size = 16) {i j : ℕ} (hi : i < BAVC.tau)
    (hj : j < 2 ^ BAVC.kOf i) :
    leafKey (BAVC.commit seed iv).2 i j = treeNode seed iv (BAVC.treePos i j) := by
  simp only [leafKey, BAVC.commit]
  rw [leavesOf_eq]
  simp only [hnone_eq, Bool.false_eq_true, ↓reduceIte]
  rw [extract_pieces _ 16 (fun i' hi' j' hj' => by
    rw [expandTree_get _ _ (treePos_lt hi' hj')]; exact treeNode_size' _ _ hs _) hi hj,
    expandTree_get _ _ (treePos_lt hi hj)]

/-- The hidden leaves' commitments of the executable commitment. -/
lemma comsOf_commit (seed iv delta : ByteArray) (i : Fin BAVC.tau) :
    comsOf (BAVC.commit seed iv).2.coms delta i =
      blk 32 (BAVC.leafCom iv (treeNode seed iv (hLeaf delta i)) i) := by
  simp only [comsOf, BAVC.commit]
  rw [leavesOf_eq]
  simp only [hnone_eq, Bool.false_eq_true, ↓reduceIte]
  rw [show BAVC.hashLen = 32 from rfl, extract_pieces _ 32 (fun _ _ _ _ => leafCom_size _ _ _) i.isLt
    (deltaIndex_lt delta i), expandTree_get _ _ (treePos_lt i.isLt (deltaIndex_lt delta i))]
  rfl

lemma openNodes_size (delta : ByteArray) : (BAVC.openNodes delta).size = openCount delta := by
  rw [← openSeeds_size (Array.replicate BAVC.numNodes BAVC.zeroBlock) delta, openSeeds_eq,
    Array.size_map]

/-- The opened seeds of the executable commitment. -/
lemma seedsOf_commit (seed iv delta : ByteArray) (k : Fin 105) :
    seedsOf (BAVC.commit seed iv).1 delta k = if k.val < openCount delta then
      blk 16 (treeNode seed iv (oNode delta k)) else fun _ => 0 := by
  simp only [seedsOf, BAVC.commit, openSeeds_eq]
  unfold oNode
  have hlt := openNodes_lt delta
  have hsz := openNodes_size delta
  generalize BAVC.openNodes delta = nodes at hlt hsz ⊢
  split_ifs with hk
  · rw [← hsz] at hk
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem hk,
      Option.map_some, Option.getD_some, getElem!_pos nodes _ hk,
      expandTree_get _ _ (hlt _ (Array.getElem_mem hk))]
  · rw [← hsz] at hk
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_none (by omega)]
    rfl

/-- **The hidden part is `hiddenOutE`** for a PRG that is `prgR` of the table's row at every
16-byte key (`hE`). -/
theorem hiddenOut_rows (E : Cipher)
    (hE : ∀ (k : Blk) (iv : ByteArray) (t c : UInt32) (n : ℕ),
      HasPrg.prg (ba k) iv t c n = prgR (E k) iv t c n)
    (p : Params) (iv delta : ByteArray) (seed : Blk) :
    hiddenOut p iv delta seed = hiddenOutE E p iv delta seed := by
  have hs : (ba seed).size = 16 := size_ba _
  set R : Fin nN → Blk → Blk := fun _ _ => seed
  have hrow : ∀ n t c m, prgR (rowAt (xIn iv) nN ∅ E R seed n) iv t c m =
      HasPrg.prg (treeNode (ba seed) iv n) iv t c m := fun n t c m => by
    rw [rowAt_of_not_mem (Finset.notMem_empty _), ← hE, keyAt_rows E hE]
  set ρ := rowAt (xIn iv) nN ∅ E R seed
  have hus : ((Array.range BAVC.tau).map fun i =>
      bytesOfWords (Prover.smallVoleUWords p iv i (leafKey (BAVC.commit (ba seed) iv).2 i))) =
      usR p iv ρ := by
    refine Array.map_congr_left fun i hi => ?_
    have hi := Array.mem_range.1 hi
    refine congrArg bytesOfWords ?_
    unfold Prover.smallVoleUWords smallR
    refine List.foldl_ext _ _ _ fun acc j hj => ?_
    have hj := List.mem_range.1 hj
    rw [prgWords, leafKey_commit _ _ hs hi hj, hrow]
  have hcoms : comsOf (BAVC.commit (ba seed) iv).2.coms delta = fun i : Fin BAVC.tau =>
      blk 32 (prgR (ρ (hLeaf delta i)) iv (i.val + BAVC.numLeaves - 1).toUInt32 0 2) := by
    funext i
    rw [comsOf_commit, hrow, BAVC.leafCom]
  have hseeds : seedsOf (BAVC.commit (ba seed) iv).1 delta = fun k : Fin 105 =>
      if k.val < openCount delta then ρ ((oNode delta k - 1) / 2) (xIn iv (oNode delta k))
      else fun _ => 0 := by
    funext k
    rw [seedsOf_commit]
    split_ifs with hk
    · have hk' : k.val < (BAVC.openNodes delta).size := by rw [openNodes_size]; exact hk
      have h1 := (openNodes_get delta hk').1
      rw [← keyAt_rows E hE iv R seed, blk_ba, keyAt_pos (by rw [oNode]; omega)]
    · rfl
  have e1 : hiddenOut p iv delta seed = (comsOf (BAVC.commit (ba seed) iv).2.coms delta,
      seedsOf (BAVC.commit (ba seed) iv).1 delta, dropSib (padsOfArrays p ((Array.range BAVC.tau).map
        fun i => bytesOfWords (Prover.smallVoleUWords p iv i (leafKey (BAVC.commit (ba seed) iv).2 i)))
        (HasPrg.prg (ba seed) iv (((1 : UInt32) <<< 31) - 1) 0 ((8 * p.nMask + 127) / 128)) #[])) := rfl
  have e2 : hiddenOutE E p iv delta seed = hidOfRows p iv delta ρ := rfl
  have hhi : HasPrg.prg (ba seed) iv (((1 : UInt32) <<< 31) - 1) 0 ((8 * p.nMask + 127) / 128) =
      prgR (ρ 0) iv (((1 : UInt32) <<< 31) - 1) 0 ((8 * p.nMask + 127) / 128) := by
    rw [hrow 0, treeNode]
  rw [e1, e2, hus, hcoms, hseeds, hhi, hidOfRows]

end Generic

/-- **With AES, the nodes are the executable tree's.** -/
theorem keyAt_aes (iv : ByteArray) (R : Fin nN → Blk → Blk) (seed : Blk) :
    ∀ n, ba (keyAt (xIn iv) nN ∅ aesTable R seed n) = treeNode (ba seed) iv n :=
  keyAt_rows aesTable prg_eq_prgR iv R seed

/-- **With the ideal-cipher PRG of `E`, the nodes are the tree of `IC.keyAt`.** -/
theorem keyAt_ic (E : Cipher) (iv : ByteArray) (R : Fin nN → Blk → Blk) (seed : Blk) :
    ∀ n, ba (keyAt (xIn iv) nN ∅ E R seed n) = @treeNode (icPrg E) (ba seed) iv n :=
  @keyAt_rows (icPrg E) E (icPrg_prg E) iv R seed

lemma rowAt_aes (iv : ByteArray) (R : Fin nN → Blk → Blk) (seed : Blk) (n : ℕ) :
    rowAt (xIn iv) nN ∅ aesTable R seed n = aesTable (keyAt (xIn iv) nN ∅ aesTable R seed n) :=
  rowAt_of_not_mem (Finset.notMem_empty _)

/-- **The bridge: the executable hidden part is `hiddenOutE` with AES.** -/
theorem hiddenOut_eq (p : Params) (iv delta : ByteArray) (seed : Blk) :
    hiddenOut p iv delta seed = hiddenOutE aesTable p iv delta seed :=
  hiddenOut_rows aesTable prg_eq_prgR p iv delta seed

/-- **With the ideal-cipher PRG of `E`, the hidden part is `hiddenOutE E`**: the commitment's
hidden part computed by the executable code with the cipher `E` is the one of the GGM hybrid. -/
theorem hiddenOut_ic (E : Cipher) (p : Params) (iv delta : ByteArray) (seed : Blk) :
    @hiddenOut (icPrg E) p iv delta seed = hiddenOutE E p iv delta seed :=
  @hiddenOut_rows (icPrg E) E (icPrg_prg E) p iv delta seed

/-! ## The side conditions of the hybrid -/

lemma blk16_inj {a b : ByteArray} (ha : a.size = 16) (hb : b.size = 16) (h : blk 16 a = blk 16 b) :
    a = b := by
  rw [← ba_blk_of_size ha, ← ba_blk_of_size hb, h]

/-- Two CTR blocks (as tape blocks) are equal only for equal counters and tweaks. -/
lemma blkCtr_inj (iv : ByteArray) {c t c' t' : UInt32}
    (h : blk 16 (AES.ctrBlock iv c t) = blk 16 (AES.ctrBlock iv c' t')) : c = c' ∧ t = t' :=
  ctrBlock_inj iv (blk16_inj (ctrBlock_size _ _ _) (ctrBlock_size _ _ _) h)

lemma blkCtr_ne_of_roles (iv : ByteArray) {r s : Seed.Commitments.Role} (hrs : r ≠ s)
    {t t' c c' : UInt32} (ht : t.toNat ∈ Seed.Commitments.tweaks r)
    (ht' : t'.toNat ∈ Seed.Commitments.tweaks s) :
    blk 16 (AES.ctrBlock iv c t) ≠ blk 16 (AES.ctrBlock iv c' t') := fun h =>
  ctrBlock_ne_of_roles iv hrs ht ht' (blk16_inj (ctrBlock_size _ _ _) (ctrBlock_size _ _ _) h)

lemma zero_add_toUInt32_inj {a b : ℕ} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (h : (0 : UInt32) + a.toUInt32 = 0 + b.toUInt32) : a = b := by
  rw [zero_add, zero_add] at h
  have := congrArg UInt32.toNat h
  rwa [toNat_toUInt32 ha, toNat_toUInt32 hb] at this

/-- **Siblings have different inputs.** -/
theorem xIn_sib (iv : ByteArray) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m ≠ n)
    (hp : (m - 1) / 2 = (n - 1) / 2) : xIn iv m ≠ xIn iv n := by
  intro h
  have := (blkCtr_inj iv h).1
  have := zero_add_toUInt32_inj (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num))
    (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)) this
  omega

/-- A GGM tweak (an internal node's index) lies in the GGM role's range. -/
lemma ggm_tweak {n : ℕ} (hn : n < BAVC.numLeaves - 1) :
    n.toUInt32.toNat ∈ Seed.Commitments.tweaks .ggm := (children_tweak .empty .empty hn).2

lemma mask_tweak : (((1 : UInt32) <<< 31) - 1).toNat ∈ Seed.Commitments.tweaks .mask := by
  simp [Seed.Commitments.tweaks]; decide

lemma hLeaf_ge (delta : ByteArray) (i : ℕ) : BAVC.numLeaves - 1 ≤ hLeaf delta i := treePos_ge _ _

lemma hLeaf_lt (delta : ByteArray) {i : ℕ} (hi : i < BAVC.tau) : hLeaf delta i < nN :=
  treePos_lt hi (deltaIndex_lt delta i)

lemma hid_hLeaf (delta : ByteArray) {i : ℕ} (hi : i < BAVC.tau) : hid delta (hLeaf delta i) = true := by
  rw [hLeaf, hid_treePos delta hi (deltaIndex_lt delta i)]; simp

lemma par_lt_internal {n : ℕ} (hn : n < nN) : (n - 1) / 2 < BAVC.numLeaves - 1 := by
  have : nN = 4607 := rfl
  have : BAVC.numLeaves - 1 = 2303 := rfl
  omega

/-- The opened nodes are off the hidden paths, and their parents are on them. -/
theorem openNodes_spec (delta : ByteArray) {c : ℕ} (hc : c ∈ BAVC.openNodes delta) :
    hid delta c = false ∧ hid delta ((c - 1) / 2) = true := by
  rw [← Array.mem_toList_iff, openNodes_toList, List.mem_filterMap] at hc
  obtain ⟨m, hm, ho⟩ := hc
  have hm := List.mem_range.1 hm
  have hL : BAVC.numLeaves - 1 = 2303 := rfl
  simp only [opened] at ho
  set n := BAVC.numLeaves - 2 - m with hn
  have hint := hid_internal delta (show n < BAVC.numLeaves - 1 by omega)
  split at ho
  · rename_i hne
    simp only [Option.some.injEq] at ho
    subst ho
    split
    · rename_i h1
      have h2 : hid delta (2 * n + 2) = false := by simpa [h1] using hne
      refine ⟨h2, ?_⟩
      rw [show (2 * n + 2 - 1) / 2 = n by omega, hint, h1]; rfl
    · rename_i h1
      have h1 : hid delta (2 * n + 1) = false := by simpa using h1
      refine ⟨h1, ?_⟩
      have h2 : hid delta (2 * n + 2) = true := by simpa [h1] using hne
      rw [show (2 * n + 1 - 1) / 2 = n by omega, hint, h2, Bool.or_true]
  · simp at ho

/-- The opened nodes are distinct. -/
theorem openNodes_nodup (delta : ByteArray) : (BAVC.openNodes delta).toList.Nodup := by
  rw [openNodes_toList, List.Nodup, List.pairwise_filterMap]
  refine List.Pairwise.imp_of_mem (fun {m m'} hm hm' hne c hc c' hc' e => hne ?_) List.nodup_range
  have hm := List.mem_range.1 hm
  have hm' := List.mem_range.1 hm'
  subst e
  simp only [opened] at hc hc'
  have hL : BAVC.numLeaves - 1 = 2303 := rfl
  split at hc <;> split at hc' <;> simp only [Option.some.injEq, reduceCtorEq] at hc hc'
  -- The opened node determines its parent `L − 2 − m`.
  split at hc <;> split at hc' <;> omega

lemma oNode_mem (delta : ByteArray) {k : ℕ} (hk : k < openCount delta) :
    oNode delta k ∈ BAVC.openNodes delta := by
  rw [oNode, getElem!_pos _ _ (by rw [openNodes_size]; exact hk)]
  exact Array.getElem_mem _

lemma oNode_pos (delta : ByteArray) {k : ℕ} (hk : k < openCount delta) : 1 ≤ oNode delta k :=
  openNodes_pos delta _ (oNode_mem delta hk)

lemma oNode_lt (delta : ByteArray) {k : ℕ} (hk : k < openCount delta) : oNode delta k < nN :=
  openNodes_lt delta _ (oNode_mem delta hk)

lemma oNode_inj (delta : ByteArray) {k k' : ℕ} (hk : k < openCount delta) (hk' : k' < openCount delta)
    (h : oNode delta k = oNode delta k') : k = k' := by
  have hs := openNodes_size delta
  have hnd := openNodes_nodup delta
  unfold oNode at h
  generalize BAVC.openNodes delta = nodes at hs hnd h
  rw [getElem!_pos _ _ (by omega), getElem!_pos _ _ (by omega)] at h
  have := (List.Nodup.getElem_inj_iff hnd (i := k) (j := k') (hi := by simp; omega)
    (hj := by simp; omega)).1 (by simpa using h)
  exact this

/-- **The hidden part never reads a hidden node's value**: changing the parent's row at a hidden
node's input changes nothing (the opened seeds are the other children; `u_hi` uses the mask
tweak; the leaves are not parents). -/
theorem hidOfRows_point (p : Params) (iv delta : ByteArray) {n : ℕ} (hn : n < nN) (hn0 : n ≠ 0)
    (hh : hid delta n = true) (ρ : ℕ → Blk → Blk) (y : Blk) :
    hidOfRows p iv delta (Function.update ρ ((n - 1) / 2)
      (Function.update (ρ ((n - 1) / 2)) (xIn iv n) y)) = hidOfRows p iv delta ρ := by
  set q := (n - 1) / 2 with hqdef
  have hq : q < BAVC.numLeaves - 1 := par_lt_internal hn
  set ρ' := Function.update ρ q (Function.update (ρ q) (xIn iv n) y)
  have hleaf : ∀ m, BAVC.numLeaves - 1 ≤ m → ρ' m = ρ m := fun m hm =>
    Function.update_of_ne (by omega) _ _
  have h1 : ∀ i : Fin BAVC.tau, ρ' (hLeaf delta i) = ρ (hLeaf delta i) := fun i =>
    hleaf _ (hLeaf_ge _ _)
  have h3 : usR p iv ρ' = usR p iv ρ := by
    unfold usR
    refine Array.map_congr_left fun i _ => ?_
    rw [show (fun j => ρ' (BAVC.treePos i j)) = fun j => ρ (BAVC.treePos i j) from
      funext fun j => hleaf _ (treePos_ge _ _)]
  have h4 : prgR (ρ' 0) iv (((1 : UInt32) <<< 31) - 1) 0 ((8 * p.nMask + 127) / 128) =
      prgR (ρ 0) iv (((1 : UInt32) <<< 31) - 1) 0 ((8 * p.nMask + 127) / 128) := by
    by_cases hq0 : q = 0
    · refine prgR_congr fun j _ => ?_
      simp only [ρ', hq0, Function.update_self]
      refine Function.update_of_ne (fun e => ?_) _ _
      refine blkCtr_ne_of_roles iv (r := .mask) (s := .ggm) (c := 0 + j.toUInt32)
        (c' := 0 + ((n - 1) % 2).toUInt32) (by decide) mask_tweak (ggm_tweak (n := q) hq) ?_
      rw [e, xIn, ← hqdef]
    · simp only [ρ', Function.update_of_ne (Ne.symm hq0)]
  have h2 : ∀ k : Fin 105, k.val < openCount delta →
      ρ' ((oNode delta k - 1) / 2) (xIn iv (oNode delta k)) =
        ρ ((oNode delta k - 1) / 2) (xIn iv (oNode delta k)) := by
    intro k hk
    by_cases hpk : (oNode delta k - 1) / 2 = q
    · simp only [ρ', hpk, Function.update_self]
      refine Function.update_of_ne (xIn_sib iv (by have := oNode_pos delta hk; omega) hn0
        (fun e => ?_) (by rw [hpk])) _ _
      have := (openNodes_spec delta (oNode_mem delta hk)).1
      rw [e, hh] at this
      exact absurd this (by decide)
    · simp only [ρ', Function.update_of_ne hpk]
  unfold hidOfRows
  rw [h3, h4]
  refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun k => ?_) rfl)
  · simp only [h1]
  · simp only
    split_ifs with hk
    · exact h2 k hk
    · rfl

/-- **The hidden part reads the nodes below `2L − 1` only.** -/
theorem hidOfRows_congr (p : Params) (iv delta : ByteArray) (ρ ρ' : ℕ → Blk → Blk)
    (h : ∀ m < nN, ρ m = ρ' m) : hidOfRows p iv delta ρ = hidOfRows p iv delta ρ' := by
  have h3 : usR p iv ρ = usR p iv ρ' := by
    unfold usR
    refine Array.map_congr_left fun i hi => ?_
    have hi := Array.mem_range.1 hi
    refine congrArg bytesOfWords ?_
    unfold smallR
    refine List.foldl_ext _ _ _ fun acc j hj => ?_
    simp only [h _ (treePos_lt hi (List.mem_range.1 hj))]
  unfold hidOfRows
  rw [h3, h 0 (by decide)]
  refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun k => ?_) rfl)
  · simp only [h _ (hLeaf_lt delta i.isLt)]
  · simp only
    split_ifs with hk
    · rw [h _ (by have := oNode_lt delta hk; omega)]
    · rfl

/-! ## The hybrid over the hidden paths -/

/-- **The hidden paths**: the hidden leaves and their ancestors. -/
def hidSet (delta : ByteArray) : Finset ℕ := (range nN).filter fun n => hid delta n = true

lemma card_blk : Fintype.card Blk = 2 ^ 128 := by rw [Prob.card_bytes]

/-- **GGM puncturing of the BAVC tree (H4's hybrid)**: replacing the rows of all nodes on the
hidden paths by independent uniform rows costs `|hidden paths| · (2L − 1 + q) / 2¹²⁸` against a
distinguisher of the hidden part that reads the cipher table at `q` keys. -/
theorem hide_puncture (p : Params) (iv delta : ByteArray) (A : Hidden p → Cipher → Prop)
    (Q : Hidden p → Cipher → Finset Blk)
    (hQ : ∀ o G G', (∀ k ∈ Q o G, G k = G' k) → (A o G ↔ A o G')) {q : ℕ}
    (hq : ∀ o G, (Q o G).card ≤ q) :
    |exper (xIn iv) nN ∅ (hidOfRows p iv delta) A -
        exper (xIn iv) nN (hidSet delta) (hidOfRows p iv delta) A| ≤
      (hidSet delta).card * ((nN + q : ℕ) / 2 ^ 128) := by
  have h := puncture (x := xIn iv) (N := nN) (fun n => hid delta n = true)
    (fun n hn hs h0 => hid_parent delta (by omega) hn hs)
    (fun n _ _ h0 m hm hmn hp => xIn_sib iv hm h0 hmn hp) (hidOfRows p iv delta)
    (fun n hn hs h0 ρ y => hidOfRows_point p iv delta hn h0 hs ρ y)
    (hidOfRows_congr p iv delta) A Q hQ hq
  rw [card_blk] at h
  exact_mod_cast h

/-- A node on a hidden path is an ancestor of a hidden leaf (`n + 1` is a prefix of the leaf's
`ℓ + 1` in binary), at most `12` levels up. -/
theorem hid_anc (delta : ByteArray) : ∀ n, n < nN → hid delta n = true →
    ∃ i < BAVC.tau, ∃ j < 13, n + 1 = (hLeaf delta i + 1) / 2 ^ j := by
  have hN : nN = 4607 := rfl
  have hL : BAVC.numLeaves - 1 = 2303 := rfl
  intro n
  induction n using Nat.strong_decreasing_induction with
  | base => exact ⟨nN, fun m hm hm' => absurd hm' (by omega)⟩
  | step n ih =>
    intro hn hh
    by_cases hleaf : BAVC.numLeaves - 1 ≤ n
    · rw [hid_leaf delta hleaf, (hiddenLeafMarks_spec delta).2] at hh
      obtain ⟨i, hi, e⟩ := of_decide_eq_true hh
      exact ⟨i, hi, 0, by norm_num, by rw [hLeaf, e]; simp⟩
    · rw [hid_internal delta (by omega), Bool.or_eq_true] at hh
      have hc : ∃ c, (c = 2 * n + 1 ∨ c = 2 * n + 2) ∧ hid delta c = true := by
        rcases hh with h | h
        · exact ⟨_, Or.inl rfl, h⟩
        · exact ⟨_, Or.inr rfl, h⟩
      obtain ⟨c, hcn, hcid⟩ := hc
      obtain ⟨i, hi, j, hj, e⟩ := ih c (by omega) (by omega) hcid
      have hlt := hLeaf_lt delta hi
      refine ⟨i, hi, j + 1, ?_, ?_⟩
      · by_contra hj'
        have hj12 : j = 12 := by omega
        subst hj12
        have : (hLeaf delta i + 1) / 2 ^ 12 = 0 ∨ (hLeaf delta i + 1) / 2 ^ 12 = 1 := by
          have : (hLeaf delta i + 1) / 2 ^ 12 < 2 := by
            rw [Nat.div_lt_iff_lt_mul (by norm_num)]; omega
          omega
        omega
      · rw [pow_succ, ← Nat.div_div_eq_div_mul, ← e]
        omega

/-- **At most `τ · 13 = 221` nodes are on the hidden paths.** -/
theorem hidSet_card (delta : ByteArray) : (hidSet delta).card ≤ 221 := by
  have hsub : hidSet delta ⊆ (univ : Finset (Fin BAVC.tau × Fin 13)).image
      fun ij => (hLeaf delta ij.1 + 1) / 2 ^ ij.2.val - 1 := by
    intro n hn
    obtain ⟨hn, hh⟩ := Finset.mem_filter.1 hn
    obtain ⟨i, hi, j, hj, e⟩ := hid_anc delta n (Finset.mem_range.1 hn) hh
    exact Finset.mem_image.2 ⟨(⟨i, hi⟩, ⟨j, hj⟩), Finset.mem_univ _, by simp only; omega⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  rfl

end VoleMole.ZK.Sim
