import VoleMole.ROM.VerifyIC

/-!
# The cipher rows the straight-line extractor reads

`ROM/`'s straight-line extractor computes, from the prover's cipher log `log`, the cipher table
`E` and the proof, the leaf keys (`keysOf`), the known trees (`knownOf`) and, with the
ideal-cipher PRG `icPrg E.cipher`, each tree's candidate (`Chain.u`, `uBit`). Here the cells of `E`
it reads are given as **rows** (cipher keys), with a count:

* `logKeys log`: the keys of the logged cells. `extractKey`, hence `knownOf`, reads `E` only in
  these rows (`extractKey_congr`, `knownOf_congr`).
* `needRows A`: the rows of the cells the verifier's PRG calls read on the derived tree `A`
  (`needCells`): one per known internal node, one per leaf position. `mem_needRows`: every cell of
  `needCells p iv A` is in a row of `needRows A`, for every `p`; `length_needRows_le`: at most
  `(L − 1) + L = 4607` rows.
* `treeRows E iv opening delta`: `needRows` of the reconstruction's derived tree with `icPrg E`.
  `keysOf_congr`: two tables that agree in the rows of `logKeys log` and of `treeRows` give the same
  leaf keys (the reconstruction reads `treeRows`, `reconstruct_congr_cells`; the extraction reads
  the logged rows).
* `zeroRow`: the row of the zero key. `keysOf_row`: every leaf key is a logged key or the zero
  key, so `uBit` with the leaf keys (the candidates' PRG expansions) reads `E` only in the logged
  rows and `zeroRow` (`uBit_congr_keysOf`).
* **`extractRows`**: `logKeys log ∪ treeRows ∪ {zeroRow}`, at most `|logKeys log| + 4608` rows
  (`card_extractRows_le`); `keysOf`, `knownOf` and every `uBit` of the leaf keys agree for two tables
  that agree in these rows (`extract_congr_rows`).
-/

open Finset OracleSpec

namespace VoleMole.ROM.IC

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim VoleMole.ROM

/-! ## The rows of the logged cells -/

/-- **The keys of the logged cells.** -/
def logKeys (log : QueryLog cspec) : Finset Blk := (log.map fun q => q.1.1).toFinset

lemma mem_logKeys {log : QueryLog cspec} {q : (_ : Cell) × Blk} (hq : q ∈ log) :
    q.1.1 ∈ logKeys log :=
  List.mem_toFinset.2 (List.mem_map.2 ⟨q, hq, rfl⟩)

lemma find?_congr_mem {β : Type} {p p' : β → Bool} :
    ∀ {l : List β}, (∀ x ∈ l, p x = p' x) → l.find? p = l.find? p'
  | [], _ => rfl
  | x :: l, h => by
    rw [List.find?_cons, List.find?_cons, h x List.mem_cons_self,
      find?_congr_mem fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- **The extraction reads the table in the logged rows only.** -/
theorem extractKey_congr {log : QueryLog cspec} {E E' : CTable}
    (h : ∀ x : Cell, x.1 ∈ logKeys log → E x = E' x) (iv : ByteArray) (i : ℕ) (a : ByteArray) :
    extractKey log E iv i a = extractKey log E' iv i a := by
  unfold extractKey
  refine congrArg _ (find?_congr_mem fun q hq => ?_)
  have hq := mem_logKeys hq
  rw [h (q.1.1, lp iv i 0) hq, h (q.1.1, lp iv i 1) hq]

/-- **The known trees read the table in the logged rows only.** -/
theorem knownOf_congr {log : QueryLog cspec} {E E' : CTable}
    (h : ∀ x : Cell, x.1 ∈ logKeys log → E x = E' x) (iv opening : ByteArray) :
    knownOf log E iv opening = knownOf log E' iv opening := by
  unfold knownOf
  simp only [extractKey_congr h]

/-! ## The rows of the verifier's cells -/

/-- The cells of a PRG call are in the row of its key. -/
lemma mem_callCells {key iv : ByteArray} {t c : UInt32} {n : ℕ} {x : Cell}
    (hx : x ∈ callCells key iv t c n) : x.1 = blk 16 key := by
  unfold callCells at hx
  split_ifs at hx
  · simp only [ctrCells, List.mem_map, List.mem_range] at hx
    obtain ⟨j, -, rfl⟩ := hx
    rfl
  · simp at hx

/-- **The rows of the verifier's cells** on a derived tree `A`: the known internal nodes' and every
leaf position's (the node values as keys). -/
def needRows (A : Array (Option ByteArray)) : List Blk :=
  ((List.range (BAVC.numLeaves - 1)).filterMap fun n => (A[n]!).map (blk 16)) ++
    ((List.range BAVC.tau).flatMap fun i => (List.range (2 ^ BAVC.kOf i)).map fun j =>
      blk 16 (A.map (·.getD BAVC.zeroBlock))[BAVC.treePos i j]!)

/-- **Every cell the verifier reads is in a row of `needRows`**, whatever the parameters. -/
theorem mem_needRows {p : Params} {iv : ByteArray} {A : Array (Option ByteArray)} {x : Cell}
    (hx : x ∈ needCells p iv A) : x.1 ∈ needRows A := by
  unfold needCells at hx
  unfold needRows
  simp only [List.mem_append, List.mem_flatMap, List.mem_range] at hx
  rcases hx with ⟨n, hn, hx⟩ | ⟨i, hi, j, hj, hx⟩
  · refine List.mem_append_left _ (List.mem_filterMap.2 ⟨n, List.mem_range.2 hn, ?_⟩)
    rcases hA : A[n]! with _ | node
    · rw [hA] at hx; simp at hx
    · rw [hA] at hx
      rw [mem_callCells hx]
      rfl
  · refine List.mem_append_right _ (List.mem_flatMap.2 ⟨i, List.mem_range.2 hi,
      List.mem_map.2 ⟨j, List.mem_range.2 hj, ?_⟩⟩)
    rcases hx with hx | hx <;> exact (mem_callCells hx).symm

/-- **At most `(L − 1) + L` rows.** -/
theorem length_needRows_le (A : Array (Option ByteArray)) :
    (needRows A).length ≤ (BAVC.numLeaves - 1) + BAVC.numLeaves := by
  unfold needRows
  rw [List.length_append]
  refine Nat.add_le_add ((List.length_filterMap_le _ _).trans (by simp)) (le_of_eq ?_)
  rw [List.length_flatMap, ← sum_leaves]
  simp

/-- **The rows the reconstruction reads**: `needRows` of the derived tree with `icPrg E`. -/
def treeRows (E : Cipher) (iv opening delta : ByteArray) : Finset Blk :=
  (needRows (@derivedN (icPrg E) iv opening delta (BAVC.numLeaves - 1))).toFinset

lemma card_treeRows_le (E : Cipher) (iv opening delta : ByteArray) :
    (treeRows E iv opening delta).card ≤ 4607 :=
  (List.toFinset_card_le _).trans ((length_needRows_le _).trans (by decide))

lemma mem_treeRows {E : Cipher} {p : Params} {iv opening delta : ByteArray} {x : Cell}
    (hx : x ∈ cellsE E p iv opening delta) : x.1 ∈ treeRows E iv opening delta :=
  List.mem_toFinset.2 (mem_needRows hx)

/-- **The reconstruction reads the table in `treeRows` only.** -/
theorem reconstruct_congr_rows {E E' : CTable} {iv opening delta : ByteArray}
    (h : ∀ x : Cell, x.1 ∈ treeRows E.cipher iv opening delta → E x = E' x) :
    @BAVC.reconstruct (icPrg E.cipher) iv opening delta =
      @BAVC.reconstruct (icPrg E'.cipher) iv opening delta :=
  reconstruct_congr_cells (p := pomfritParams) fun x hx => h x (mem_treeRows hx)

/-- **The leaf keys read the table in the logged rows and `treeRows` only.** -/
theorem keysOf_congr {log : QueryLog cspec} {E E' : CTable} {iv opening delta : ByteArray}
    (h : ∀ x : Cell, x.1 ∈ logKeys log ∪ treeRows E.cipher iv opening delta → E x = E' x) :
    keysOf log E iv opening delta = keysOf log E' iv opening delta := by
  have hr := reconstruct_congr_rows (E := E) (E' := E') (iv := iv) (opening := opening)
    (delta := delta) fun x hx => h x (mem_union_right _ hx)
  have he := extractKey_congr (log := log) fun x hx => h x (mem_union_left _ hx)
  unfold keysOf
  rw [← hr]
  simp only [he]

/-! ## The rows of the candidates' PRG expansions -/

/-- **The row of the zero key.** -/
def zeroRow : Blk := blk 16 BAVC.zeroBlock

/-- **Every leaf key is a logged key or the zero key**, as a row. -/
theorem keysOf_row (log : QueryLog cspec) (E : CTable) (iv opening delta : ByteArray) (i j : ℕ) :
    blk 16 (keysOf log E iv opening delta i j) ∈ insert zeroRow (logKeys log) := by
  have hz : blk 16 BAVC.zeroBlock ∈ insert zeroRow (logKeys log) := mem_insert_self _ _
  by_cases hv : i < BAVC.tau ∧ j < 2 ^ BAVC.kOf i
  · rcases hr : @BAVC.reconstruct (icPrg E.cipher) iv opening delta with _ | leaves
    · have : keysOf log E iv opening delta i j = BAVC.zeroBlock := by
        unfold keysOf
        rw [hr]
      rw [this]
      exact hz
    · rw [keysOf_of_reconstruct hr hv.1 hv.2]
      rcases hx : extractKey log E iv i (comAt leaves.coms i j) with _ | κ
      · exact hz
      · simp only [Option.map_some, Option.getD_some, blk_ba]
        unfold extractKey at hx
        obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hx
        exact mem_insert_of_mem (mem_logKeys (List.mem_of_find?_eq_some hq))
  · rw [keysOf_of_not_valid log E iv opening delta hv]
    exact hz

/-- **`uBit` reads the PRG only at its keys' rows**: two tables that agree in the rows of the
keys of tree `i` give the same bit. -/
theorem uBit_congr {E E' : Cipher} {p : Params} {iv : ByteArray} {corr : ℕ → ByteArray}
    {key : ℕ → ℕ → ByteArray} {i : Fin BAVC.tau} (r : ℕ)
    (h : ∀ j < 2 ^ BAVC.kOf i, ∀ z, E (blk 16 (key i j)) z = E' (blk 16 (key i j)) z) :
    @uBit (icPrg E) p iv corr key i r = @uBit (icPrg E') p iv corr key i r := by
  have hs : (∑ j ∈ range (2 ^ BAVC.kOf i),
      zb (wbit (@prgWords (icPrg E) p iv i (key i j)) r)) =
      ∑ j ∈ range (2 ^ BAVC.kOf i), zb (wbit (@prgWords (icPrg E') p iv i (key i j)) r) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj := Finset.mem_range.1 hj
    have hp := icPrgF_congr_cells (E := E) (E' := E') (key := key i j) (iv := iv)
      (t := ((1 : UInt32) <<< 31) + (i : ℕ).toUInt32) (c := 0) (n := p.voleColBlocks)
      fun x hx => by
        obtain ⟨k, z⟩ := x
        obtain rfl : k = blk 16 (key i j) := mem_callCells hx
        exact h j hj z
    unfold prgWords
    rw [hp]
  unfold uBit smallVoleU
  rw [hs]

/-- **`uBit` of the leaf keys reads the table in the logged rows and `zeroRow` only.** -/
theorem uBit_congr_keysOf {log : QueryLog cspec} {E₀ E E' : CTable} {iv opening delta : ByteArray}
    (h : ∀ x : Cell, x.1 ∈ insert zeroRow (logKeys log) → E x = E' x) (p : Params)
    (iv' : ByteArray) (corr : ℕ → ByteArray) (i : Fin BAVC.tau) (r : ℕ) :
    @uBit (icPrg E.cipher) p iv' corr (keysOf log E₀ iv opening delta) i r =
      @uBit (icPrg E'.cipher) p iv' corr (keysOf log E₀ iv opening delta) i r :=
  uBit_congr r fun j _ z => h (_, z) (keysOf_row log E₀ iv opening delta i j)

/-! ## The extractor's rows -/

/-- **The rows the straight-line extractor reads**: the logged rows, the reconstruction's and the
zero key's. -/
def extractRows (log : QueryLog cspec) (E : Cipher) (iv opening delta : ByteArray) : Finset Blk :=
  insert zeroRow (logKeys log ∪ treeRows E iv opening delta)

/-- **At most `|logKeys log| + 4608` rows.** -/
theorem card_extractRows_le (log : QueryLog cspec) (E : Cipher) (iv opening delta : ByteArray) :
    (extractRows log E iv opening delta).card ≤ (logKeys log).card + 4608 :=
  (card_insert_le _ _).trans (by
    have := (card_union_le (logKeys log) (treeRows E iv opening delta)).trans
      (Nat.add_le_add_left (card_treeRows_le E iv opening delta) _)
    omega)

/-- **The straight-line extractor reads the table in `extractRows` only**: two tables that agree
there give the same leaf keys, the same known trees and the same candidate bits (`uBit` of the
leaf keys with each table's ideal-cipher PRG). -/
theorem extract_congr_rows {log : QueryLog cspec} {E E' : CTable} {iv opening delta : ByteArray}
    (h : ∀ x : Cell, x.1 ∈ extractRows log E.cipher iv opening delta → E x = E' x) :
    keysOf log E iv opening delta = keysOf log E' iv opening delta ∧
      knownOf log E iv opening = knownOf log E' iv opening ∧
      ∀ p iv' corr i r, @uBit (icPrg E.cipher) p iv' corr (keysOf log E iv opening delta) i r =
        @uBit (icPrg E'.cipher) p iv' corr (keysOf log E' iv opening delta) i r := by
  have hk := keysOf_congr (log := log) (iv := iv) (opening := opening) (delta := delta)
    fun x hx => h x (mem_insert_of_mem hx)
  refine ⟨hk, knownOf_congr (fun x hx => h x (mem_insert_of_mem (mem_union_left _ hx))) _ _,
    fun p iv' corr i r => ?_⟩
  rw [← hk]
  exact uBit_congr_keysOf (fun x hx => h x (by
    rcases mem_insert.1 hx with hx | hx
    · exact hx ▸ mem_insert_self _ _
    · exact mem_insert_of_mem (mem_union_left _ hx))) p iv' corr i r

end VoleMole.ROM.IC
