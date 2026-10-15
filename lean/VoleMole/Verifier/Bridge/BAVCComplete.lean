import VoleMole.ZK.TapeLemmas

/-!
# Bridge: BAVC completeness (the opening of the prover's tree reconstructs its leaves)

**`bavcComplete : BAVCComplete`**: for every seed, `iv` and `Δ`, if the prover's opening
(`BAVC.openAt`, `one_tree_bavc::open`) succeeds, the verifier's reconstruction (`BAVC.reconstruct`,
`one_tree_bavc::verify`) accepts it, its commitments are the prover's, and its leaf keys are the
prover's off the hidden leaves. The executable walks are folds (`BAVC.markStep`,
`BAVC.deriveStep`); here they are read as functions of the node index:

* `treeNode`: node `n` of the GGM tree, by recursion on `n` (the root, or a block of the parent's
  PRG output); `expandTree_get`: the prover's tree is `treeNode` (`expandTree` writes each node
  once, after its parent).
* `hid Δ n`: node `n` is a hidden leaf or an ancestor of one (recursion towards the leaves);
  `walk_spec`: after `m` steps of the bottom-up walk the marks are `hid` on the processed nodes, and
  the recorded nodes are, in order, the unmarked children of the processed nodes with exactly one
  marked child. So a node outside the hidden paths whose parent is on one is opened
  (`mem_openNodes`), and the root is on one (`hid_root`).
* The opening's layout (`opening_spec`): the `τ` hidden commitments, the opened nodes, zeros.
* Placement and top-down derivation (`placed_spec`, `derive_spec`): every known seed is the tree's
  node, and after the walk `n = 0, …, L − 2` every node outside the hidden paths is known (by
  induction: its parent is either on a hidden path, so it was opened, or known before).
* The leaves (`leavesOf_eq`, `extract_pieces`): both sides concatenate per-leaf pieces of fixed
  size in the same order, and the pieces agree (the hidden commitments are read back from the
  opening; `treePos_inj`: the hidden leaves are the only marked leaves).
-/

namespace VoleMole.Verifier.Bridge

open VoleMole.Verifier VoleMole.ZK.Sim

/-! ## The tree -/

/-- Node `n` of the GGM tree from `seed`: the root, or a block of its parent's PRG output. -/
def treeNode (seed iv : ByteArray) : ℕ → ByteArray
  | 0 => seed
  | n + 1 => BAVC.block (BAVC.children iv (treeNode seed iv (n / 2)) (n / 2)) (n % 2)
decreasing_by omega

lemma treeNode_left (seed iv : ByteArray) (n : ℕ) :
    treeNode seed iv (2 * n + 1) = BAVC.block (BAVC.children iv (treeNode seed iv n) n) 0 := by
  rw [treeNode, show 2 * n / 2 = n by omega, show 2 * n % 2 = 0 by omega]

lemma treeNode_right (seed iv : ByteArray) (n : ℕ) :
    treeNode seed iv (2 * n + 2) = BAVC.block (BAVC.children iv (treeNode seed iv n) n) 1 := by
  rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, treeNode, show (2 * n + 1) / 2 = n by omega,
    show (2 * n + 1) % 2 = 1 by omega]

lemma treeNode_size (seed iv : ByteArray) {n : ℕ} (hn : 1 ≤ n) : (treeNode seed iv n).size = 16 := by
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [treeNode]
  exact block_size _ _ (by rw [children_size]; omega)

lemma numNodes_eq : BAVC.numNodes = 2 * BAVC.numLeaves - 1 := rfl

/-- **The prover's tree is `treeNode`.** -/
theorem expandTree_get (seed iv : ByteArray) {k : ℕ} (hk : k < BAVC.numNodes) :
    (BAVC.expandTree seed iv)[k]! = treeNode seed iv k := by
  unfold BAVC.expandTree
  rw [Id.run]
  simp only [bind_pure]
  rw [forIn_range_foldl _ _ _ (fun n (t : Array ByteArray) =>
    (t.set! (2 * n + 1) (BAVC.block (BAVC.children iv t[n]! n) 0)).set! (2 * n + 2)
      (BAVC.block (BAVC.children iv t[n]! n) 1)) fun _ _ => rfl]
  have key : ∀ N, N ≤ BAVC.numLeaves - 1 →
      let t := (List.range N).foldl (fun t n => (t.set! (2 * n + 1)
        (BAVC.block (BAVC.children iv t[n]! n) 0)).set! (2 * n + 2)
        (BAVC.block (BAVC.children iv t[n]! n) 1))
        ((Array.replicate BAVC.numNodes BAVC.zeroBlock).set! 0 seed)
      t.size = BAVC.numNodes ∧ ∀ k < 2 * N + 1, t[k]! = treeNode seed iv k := by
    intro N
    induction N with
    | zero =>
      intro _
      simp only [List.range_zero, List.foldl_nil]
      refine ⟨by rw [size_set!]; simp, fun k hk => ?_⟩
      obtain rfl : k = 0 := by omega
      rw [getElem!_set!]
      simp [treeNode, show 0 < BAVC.numNodes by decide]
    | succ N ih =>
      intro hN
      obtain ⟨h1, h2⟩ := ih (by omega)
      simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hl : 2 * N + 2 < BAVC.numNodes := by rw [numNodes_eq]; omega
      refine ⟨by rw [size_set!, size_set!, h1], fun k hk => ?_⟩
      rw [getElem!_set!, getElem!_set!, h2 N (by omega)]
      simp only [size_set!, h1]
      split_ifs with ha hb
      · rw [← ha.1, treeNode_right]
      · rw [← hb.1, treeNode_left]
      · exact h2 k (by omega)
  exact (key _ le_rfl).2 k (by rw [numNodes_eq] at hk; omega)

/-! ## Positions of the leaves -/

lemma treePos_lt {i j : ℕ} (hi : i < BAVC.tau) (hj : j < 2 ^ BAVC.kOf i) :
    BAVC.treePos i j < BAVC.numNodes := by
  simp only [BAVC.treePos, BAVC.tau, BAVC.numNodes, BAVC.numLeaves] at *
  rw [kOf_eq] at hj
  split_ifs at * <;> omega

lemma treePos_ge (i j : ℕ) : BAVC.numLeaves - 1 ≤ BAVC.treePos i j := by
  simp only [BAVC.treePos]; omega

/-- **Distinct leaves have distinct tree positions.** -/
theorem treePos_inj {i j i' j' : ℕ} (hi : i < BAVC.tau) (hj : j < 2 ^ BAVC.kOf i)
    (hi' : i' < BAVC.tau) (hj' : j' < 2 ^ BAVC.kOf i') (h : BAVC.treePos i j = BAVC.treePos i' j') :
    i = i' ∧ j = j' := by
  simp only [BAVC.treePos, BAVC.tau] at *
  rw [kOf_eq] at hj hj'
  split_ifs at * <;> omega

lemma deltaIndex_lt (delta : ByteArray) (i : ℕ) : BAVC.deltaIndex delta i < 2 ^ BAVC.kOf i :=
  hiddenIndex_lt _ _

/-! ## The hidden paths -/

lemma hiddenLeafMarks_spec (delta : ByteArray) :
    (BAVC.hiddenLeafMarks delta).size = BAVC.numNodes ∧ ∀ k, (BAVC.hiddenLeafMarks delta)[k]! =
      decide (∃ i < BAVC.tau, BAVC.treePos i (BAVC.deltaIndex delta i) = k) := by
  have key : ∀ N, N ≤ BAVC.tau →
      let h := (List.range N).foldl (fun h i => h.set! (BAVC.treePos i (BAVC.deltaIndex delta i)) true)
        (Array.replicate BAVC.numNodes false)
      h.size = BAVC.numNodes ∧
        ∀ k, h[k]! = decide (∃ i < N, BAVC.treePos i (BAVC.deltaIndex delta i) = k) := by
    intro N
    induction N with
    | zero =>
      intro _
      simp only [List.range_zero, List.foldl_nil]
      refine ⟨by simp, fun k => ?_⟩
      rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      split_ifs <;> simp
    | succ N ih =>
      intro hN
      obtain ⟨h1, h2⟩ := ih (by omega)
      simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hp := treePos_lt (show N < BAVC.tau by omega) (deltaIndex_lt delta N)
      refine ⟨by rw [size_set!, h1], fun k => ?_⟩
      rw [getElem!_set!, h2, h1]
      by_cases hk : BAVC.treePos N (BAVC.deltaIndex delta N) = k
      · subst hk
        simp only [hp, and_self, ↓reduceIte]
        exact (decide_eq_true ⟨N, by omega, rfl⟩).symm
      · simp only [hk, false_and, ↓reduceIte]
        congr 1
        apply propext
        constructor
        · rintro ⟨i, hi, e⟩; exact ⟨i, by omega, e⟩
        · rintro ⟨i, hi, e⟩
          refine ⟨i, ?_, e⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
          · exact hi
          · exact absurd e hk
  exact key _ le_rfl

/-- Node `n` is a hidden leaf or an ancestor of one. -/
def hid (delta : ByteArray) (n : ℕ) : Bool :=
  if n < BAVC.numLeaves - 1 then hid delta (2 * n + 1) || hid delta (2 * n + 2)
  else (BAVC.hiddenLeafMarks delta)[n]!
termination_by BAVC.numNodes - n
decreasing_by all_goals simp only [BAVC.numNodes, BAVC.numLeaves] at *; omega

lemma hid_internal (delta : ByteArray) {n : ℕ} (hn : n < BAVC.numLeaves - 1) :
    hid delta n = (hid delta (2 * n + 1) || hid delta (2 * n + 2)) := by
  rw [hid]; simp [hn]

lemma hid_leaf (delta : ByteArray) {n : ℕ} (hn : BAVC.numLeaves - 1 ≤ n) :
    hid delta n = (BAVC.hiddenLeafMarks delta)[n]! := by
  rw [hid]; simp [show ¬ n < BAVC.numLeaves - 1 by omega]

/-- The parent of a hidden node is hidden. -/
lemma hid_parent (delta : ByteArray) {c : ℕ} (hc1 : 1 ≤ c) (hc : c < BAVC.numNodes)
    (h : hid delta c = true) : hid delta ((c - 1) / 2) = true := by
  rw [hid_internal delta (by rw [numNodes_eq] at hc; omega)]
  rcases Nat.even_or_odd c with ⟨q, hq⟩ | ⟨q, hq⟩
  · rw [show 2 * ((c - 1) / 2) + 2 = c by omega]; simp [h]
  · rw [show 2 * ((c - 1) / 2) + 1 = c by omega]; simp [h]

/-- **The root is on a hidden path.** -/
theorem hid_root (delta : ByteArray) : hid delta 0 = true := by
  have up : ∀ c, c < BAVC.numNodes → hid delta c = true → hid delta 0 = true := by
    intro c
    induction c using Nat.strong_induction_on with
    | _ c ih =>
      intro hc h
      rcases Nat.eq_zero_or_pos c with rfl | hpos
      · exact h
      · exact ih _ (by omega) (by omega) (hid_parent delta hpos hc h)
  have hp := treePos_lt (show 0 < BAVC.tau by decide) (deltaIndex_lt delta 0)
  refine up _ hp ?_
  rw [hid_leaf delta (treePos_ge _ _), (hiddenLeafMarks_spec delta).2]
  exact decide_eq_true ⟨0, by decide, rfl⟩

/-- The leaf `j` of vector `i` is on a hidden path iff it is the hidden leaf `Δ_i`. -/
theorem hid_treePos (delta : ByteArray) {i j : ℕ} (hi : i < BAVC.tau) (hj : j < 2 ^ BAVC.kOf i) :
    hid delta (BAVC.treePos i j) = decide (j = BAVC.deltaIndex delta i) := by
  rw [hid_leaf delta (treePos_ge _ _), (hiddenLeafMarks_spec delta).2]
  congr 1
  apply propext
  constructor
  · rintro ⟨i', hi', e⟩
    obtain ⟨rfl, rfl⟩ := treePos_inj hi' (deltaIndex_lt delta i') hi hj e
    rfl
  · rintro rfl; exact ⟨i, hi, rfl⟩

/-- The node recorded at step `m` of the walk (if any). -/
def opened (delta : ByteArray) (m : ℕ) : Option ℕ :=
  let n := BAVC.numLeaves - 2 - m
  if hid delta (2 * n + 1) != hid delta (2 * n + 2) then
    some (if hid delta (2 * n + 1) then 2 * n + 2 else 2 * n + 1)
  else none

/-- **The walk**: after `m` steps, the marks are `hid` on the processed nodes (and on the leaves),
and the recorded nodes are those of `opened`. -/
theorem walk_spec (delta : ByteArray) : ∀ m, m ≤ BAVC.numLeaves - 1 →
    let x := (List.range m).foldl BAVC.markStep (BAVC.hiddenLeafMarks delta, #[])
    x.1.size = BAVC.numNodes ∧
      (∀ k < BAVC.numNodes, BAVC.numLeaves - 1 - m ≤ k → x.1[k]! = hid delta k) ∧
      x.2.toList = (List.range m).filterMap (opened delta) := by
  intro m
  induction m with
  | zero =>
    intro _
    simp only [List.range_zero, List.foldl_nil, List.filterMap_nil, Array.toList_empty]
    exact ⟨(hiddenLeafMarks_spec delta).1, fun k _ hk => (hid_leaf delta (by omega)).symm, trivial⟩
  | succ m ih =>
    intro hm
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
    set x := (List.range m).foldl BAVC.markStep (BAVC.hiddenLeafMarks delta, #[])
    set n := BAVC.numLeaves - 2 - m with hn
    have hL : BAVC.numLeaves - 1 = 2303 := rfl
    have hN : BAVC.numNodes = 4607 := rfl
    have hl : x.1[2 * n + 1]! = hid delta (2 * n + 1) := h2 _ (by omega) (by omega)
    have hr : x.1[2 * n + 2]! = hid delta (2 * n + 2) := h2 _ (by omega) (by omega)
    have hhn : hid delta n = (hid delta (2 * n + 1) || hid delta (2 * n + 2)) :=
      hid_internal delta (by omega)
    refine ⟨?_, ?_, ?_⟩
    · simp only [BAVC.markStep]; rw [size_set!, h1]
    · intro k hk hk'
      simp only [BAVC.markStep]
      rw [getElem!_set!, h1, ← hn, hl, hr]
      split_ifs with he
      · rw [← he.1, hhn]
      · exact h2 k hk (by omega)
    · simp only [BAVC.markStep, ← hn, hl, hr, opened]
      split
      · simp [h3]
      · simp [h3]

lemma openNodes_toList (delta : ByteArray) :
    (BAVC.openNodes delta).toList = (List.range (BAVC.numLeaves - 1)).filterMap (opened delta) := by
  rw [BAVC.openNodes]; exact (walk_spec delta _ le_rfl).2.2

/-- **A node off the hidden paths whose parent is on one is opened.** -/
theorem mem_openNodes (delta : ByteArray) {c : ℕ} (hc1 : 1 ≤ c) (hc : c < BAVC.numNodes)
    (h : hid delta c = false) (hp : hid delta ((c - 1) / 2) = true) : c ∈ BAVC.openNodes delta := by
  rw [← Array.mem_toList_iff, openNodes_toList, List.mem_filterMap]
  have hN : BAVC.numNodes = 4607 := rfl
  have hL : BAVC.numLeaves - 1 = 2303 := rfl
  set n := (c - 1) / 2 with hn
  refine ⟨BAVC.numLeaves - 2 - n, List.mem_range.2 (by omega), ?_⟩
  have e : BAVC.numLeaves - 2 - (BAVC.numLeaves - 2 - n) = n := by omega
  simp only [opened, e]
  rw [hid_internal delta (by omega)] at hp
  rcases Nat.even_or_odd c with ⟨q, hq⟩ | ⟨q, hq⟩
  · have e2 : 2 * n + 2 = c := by omega
    rw [e2, h] at hp ⊢
    simp only [Bool.or_false] at hp
    simp [hp]
  · have e1 : 2 * n + 1 = c := by omega
    rw [e1, h] at hp ⊢
    simp only [Bool.false_or] at hp
    simp [hp]

lemma openNodes_pos (delta : ByteArray) : ∀ c ∈ BAVC.openNodes delta, 1 ≤ c := by
  intro c hc
  rw [← Array.mem_toList_iff, openNodes_toList, List.mem_filterMap] at hc
  obtain ⟨m, _, hm⟩ := hc
  simp only [opened] at hm
  split at hm
  · simp only [Option.some.injEq] at hm; subst hm; split <;> omega
  · simp at hm

/-! ## Concatenations of fixed-size pieces -/

lemma extract_append_of_le (A B : ByteArray) {a b : ℕ} (hb : b ≤ A.size) :
    (A ++ B).extract a b = A.extract a b := by
  apply ByteArray.ext
  simp only [ByteArray.data_extract, ByteArray.data_append, Array.extract_append]
  have : A.size = A.data.size := rfl
  simp only [Array.extract_eq_empty_iff, Array.append_right_eq_self]
  omega

lemma extract_self (A : ByteArray) {m : ℕ} (h : A.size = m) : A.extract 0 m = A := by
  subst h
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_size

/-- Piece `k` of a concatenation of pieces of `m` bytes. -/
theorem extract_foldl_uniform (m : ℕ) : ∀ (L : List ByteArray) (acc : ByteArray),
    (∀ b ∈ L, b.size = m) → ∀ k (hk : k < L.length),
      (L.foldl (· ++ ·) acc).extract (acc.size + m * k) (acc.size + m * k + m) = L[k]
  | [], _, _, k, hk => absurd hk (by simp)
  | b :: L, acc, hL, 0, _ => by
    have e := ByteArray.extract_append_size_add (a := acc)
      (b := b ++ L.foldl (· ++ ·) ByteArray.empty) (i := 0) (j := m)
    rw [Nat.add_zero] at e
    rw [List.foldl_cons, foldl_append_eq, ByteArray.append_assoc, Nat.mul_zero, Nat.add_zero, e,
      extract_append_of_le _ _ (by rw [hL b (by simp)]), extract_self _ (hL b (by simp))]
    rfl
  | b :: L, acc, hL, k + 1, hk => by
    rw [List.foldl_cons]
    have h := extract_foldl_uniform m L (acc ++ b) (fun b' hb' => hL b' (by simp [hb'])) k
      (by simpa using hk)
    rw [ByteArray.size_append, hL b (by simp)] at h
    rw [show acc.size + m * (k + 1) = acc.size + m + m * k by ring]
    exact h

lemma size_foldl_uniform (m : ℕ) : ∀ (L : List ByteArray) (acc : ByteArray),
    (∀ b ∈ L, b.size = m) → (L.foldl (· ++ ·) acc).size = acc.size + m * L.length
  | [], _, _ => by simp
  | b :: L, acc, hL => by
    rw [List.foldl_cons, size_foldl_uniform m L _ fun b' hb' => hL b' (by simp [hb']),
      ByteArray.size_append, hL b (by simp)]
    simp only [List.length_cons]; ring

/-- The per-leaf pieces of all vectors, in spec order. -/
def pieces (f : ℕ → ℕ → ByteArray) (n : ℕ := BAVC.tau) : List ByteArray :=
  (List.range n).flatMap fun i => (List.range (2 ^ BAVC.kOf i)).map (f i)

lemma pieces_length (f : ℕ → ℕ → ByteArray) (n : ℕ) : (pieces f n).length = BAVC.leafOffset n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pieces, List.range_succ, List.flatMap_append, List.length_append] at ih ⊢
    rw [ih, leafOffset_succ]; simp

lemma pieces_getElem? (f : ℕ → ℕ → ByteArray) (n : ℕ) {i j : ℕ} (hi : i < n)
    (hj : j < 2 ^ BAVC.kOf i) : (pieces f n)[BAVC.leafOffset i + j]? = some (f i j) := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [pieces, List.range_succ, List.flatMap_append] at ih ⊢
    have hlen := pieces_length f n
    simp only [pieces] at hlen
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · have hlt : BAVC.leafOffset i + j < BAVC.leafOffset n := by
        have := leafOffset_mono (show i + 1 ≤ n by omega); rw [leafOffset_succ] at this; omega
      rw [List.getElem?_append_left (by rw [hlen]; exact hlt)]
      exact ih hi
    · rw [List.getElem?_append_right (by rw [hlen]; omega), hlen]
      simp [hj]

lemma mem_pieces {f : ℕ → ℕ → ByteArray} {n : ℕ} {b : ByteArray} (h : b ∈ pieces f n) :
    ∃ i < n, ∃ j < 2 ^ BAVC.kOf i, b = f i j := by
  simp only [pieces, List.mem_flatMap, List.mem_range, List.mem_map] at h
  obtain ⟨i, hi, j, hj, rfl⟩ := h
  exact ⟨i, hi, j, hj, rfl⟩

lemma pieces_congr {f g : ℕ → ℕ → ByteArray} {n : ℕ}
    (h : ∀ i < n, ∀ j < 2 ^ BAVC.kOf i, f i j = g i j) : pieces f n = pieces g n := by
  simp only [pieces]
  refine List.flatMap_congr fun i hi => List.map_congr_left fun j hj => ?_
  exact h i (List.mem_range.1 hi) j (List.mem_range.1 hj)

/-- Piece `(i, j)` of the leaves, for pieces of `m` bytes. -/
theorem extract_pieces (f : ℕ → ℕ → ByteArray) (m : ℕ)
    (hf : ∀ i < BAVC.tau, ∀ j < 2 ^ BAVC.kOf i, (f i j).size = m) {i j : ℕ} (hi : i < BAVC.tau)
    (hj : j < 2 ^ BAVC.kOf i) :
    ((pieces f).foldl (· ++ ·) ByteArray.empty).extract (m * (BAVC.leafOffset i + j))
      (m * (BAVC.leafOffset i + j) + m) = f i j := by
  have hget := pieces_getElem? f BAVC.tau hi hj
  have hlt : BAVC.leafOffset i + j < (pieces f).length := by
    rw [List.getElem?_eq_some_iff] at hget; exact hget.1
  have e := extract_foldl_uniform m (pieces f) ByteArray.empty (fun b hb => by
    obtain ⟨i', hi', j', hj', rfl⟩ := mem_pieces hb; exact hf i' hi' j' hj') _ hlt
  simp only [ByteArray.size_empty, Nat.zero_add] at e
  rw [e]
  exact Option.some.inj ((List.getElem?_eq_getElem hlt).symm.trans hget)

lemma foldl_pairs (K : ℕ → ℕ) (a b : ℕ → ℕ → ByteArray) :
    ∀ (l : List ℕ) (s : ByteArray × ByteArray),
      l.foldl (fun s i => (List.range (K i)).foldl (fun s j => (s.1 ++ a i j, s.2 ++ b i j)) s) s =
        ((l.flatMap fun i => (List.range (K i)).map (a i)).foldl (· ++ ·) s.1,
          (l.flatMap fun i => (List.range (K i)).map (b i)).foldl (· ++ ·) s.2) := by
  have inner : ∀ (i : ℕ) (l' : List ℕ) (s : ByteArray × ByteArray),
      l'.foldl (fun s j => (s.1 ++ a i j, s.2 ++ b i j)) s =
        ((l'.map (a i)).foldl (· ++ ·) s.1, (l'.map (b i)).foldl (· ++ ·) s.2) := by
    intro i l'
    induction l' with
    | nil => intro s; rfl
    | cons j l' ih => intro s; rw [List.foldl_cons, ih]; rfl
  intro l
  induction l with
  | nil => intro s; rfl
  | cons i l ih =>
    intro s
    rw [List.foldl_cons, ih, inner]
    simp [List.flatMap_cons, List.foldl_append]

/-- **The leaves as concatenations of per-leaf pieces.** -/
theorem leavesOf_eq (iv : ByteArray) (t : Array ByteArray) (hidden : ℕ → Option ℕ)
    (hc : ℕ → ByteArray) :
    BAVC.leavesOf iv t hidden hc =
      ⟨(pieces fun i j => if hidden i == some j then BAVC.zeroBlock else t[BAVC.treePos i j]!).foldl
          (· ++ ·) ByteArray.empty,
        (pieces fun i j => if hidden i == some j then hc i
          else BAVC.leafCom iv t[BAVC.treePos i j]! i).foldl (· ++ ·) ByteArray.empty⟩ := by
  unfold BAVC.leavesOf
  simp only [Id.run]
  rw [forIn_range_foldl _ _ _ (fun i (s : ByteArray × ByteArray) =>
    (List.range (2 ^ BAVC.kOf i)).foldl (fun s j =>
      (s.1 ++ (if hidden i == some j then BAVC.zeroBlock else t[BAVC.treePos i j]!),
       s.2 ++ (if hidden i == some j then hc i else BAVC.leafCom iv t[BAVC.treePos i j]! i))) s)
    fun i s => by
      rw [forIn_range_foldl _ _ _ (fun j (s : ByteArray × ByteArray) =>
        (s.1 ++ (if hidden i == some j then BAVC.zeroBlock else t[BAVC.treePos i j]!),
         s.2 ++ (if hidden i == some j then hc i else BAVC.leafCom iv t[BAVC.treePos i j]! i)))
        fun j s => by split <;> simp_all]
      rfl]
  rw [foldl_pairs]
  have e : ∀ n, ByteArray.emptyWithCapacity n = ByteArray.empty := fun _ => rfl
  simp only [e, pieces, pure_bind]
  rfl

/-! ## The prover's opening -/

lemma openNodes_get (delta : ByteArray) {k : ℕ} (hk : k < (BAVC.openNodes delta).size) :
    1 ≤ (BAVC.openNodes delta)[k]! ∧ (BAVC.openNodes delta)[k]! < BAVC.numNodes := by
  have hpos := openNodes_pos delta
  have hlt := openNodes_lt delta
  generalize BAVC.openNodes delta = nodes at *
  rw [getElem!_pos nodes k hk]
  exact ⟨hpos _ (Array.getElem_mem hk), hlt _ (Array.getElem_mem hk)⟩

/-- **The layout of the prover's opening**: the `τ` hidden leaves' commitments, the seeds of
`openNodes Δ` (at most `T_OPEN = 105`), zeros. -/
theorem opening_spec (seed iv delta o : ByteArray)
    (ho : BAVC.openAt (BAVC.commit seed iv).1 (BAVC.commit seed iv).2.coms delta = some o) :
    o.size = BAVC.openSize ∧ (BAVC.openNodes delta).size ≤ 105 ∧
      (∀ i < BAVC.tau, o.extract (BAVC.hashLen * i) (BAVC.hashLen * i + BAVC.hashLen) =
        (BAVC.commit seed iv).2.coms.extract
          (BAVC.hashLen * (BAVC.leafOffset i + BAVC.deltaIndex delta i))
          (BAVC.hashLen * (BAVC.leafOffset i + BAVC.deltaIndex delta i) + BAVC.hashLen)) ∧
      (∀ k < (BAVC.openNodes delta).size,
        o.extract (BAVC.tau * BAVC.hashLen + 16 * k) (BAVC.tau * BAVC.hashLen + 16 * k + 16) =
          treeNode seed iv (BAVC.openNodes delta)[k]!) ∧
      (∀ q, BAVC.tau * BAVC.hashLen + 16 * (BAVC.openNodes delta).size ≤ q → o.get! q = 0) := by
  have hcs : (BAVC.commit seed iv).2.coms.size = BAVC.hashLen * BAVC.numLeaves :=
    commit_coms_size seed iv
  have hnget := fun k (hk : k < (BAVC.openNodes delta).size) => openNodes_get delta hk
  have htree : ∀ k < BAVC.numNodes, (BAVC.commit seed iv).1[k]! = treeNode seed iv k :=
    fun k hk => expandTree_get seed iv hk
  unfold BAVC.openAt at ho
  rw [openSeeds_eq] at ho
  generalize (BAVC.commit seed iv).2.coms = coms at *
  generalize (BAVC.commit seed iv).1 = t at *
  generalize BAVC.openNodes delta = nodes at *
  simp only at ho
  split_ifs at ho with hbig
  simp only [Option.some.injEq] at ho
  subst ho
  set seeds := nodes.map fun k => t[k]! with hseeds
  have hsz : seeds.size = nodes.size := by rw [hseeds, Array.size_map]
  have hseedk : ∀ k < nodes.size, seeds[k]! = treeNode seed iv nodes[k]! := by
    intro k hk
    rw [hseeds, getElem!_map' _ _ hk, htree _ (hnget k hk).2]
  have hseedL : ∀ k (hk : k < seeds.toList.length), seeds.toList[k] = treeNode seed iv nodes[k]! := by
    intro k hk
    have hk' : k < nodes.size := by simpa [hsz] using hk
    rw [Array.getElem_toList, ← getElem!_pos seeds k (by omega), hseedk k hk']
  have hseed16 : ∀ b ∈ seeds.toList, b.size = 16 := by
    intro b hb
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
    have hk' : k < nodes.size := by simpa [hsz] using hk
    rw [hseedL k hk]
    exact treeNode_size _ _ (hnget k hk').1
  -- The hidden commitments.
  set f : ℕ → ByteArray := fun i =>
    coms.extract (BAVC.hashLen * (BAVC.leafOffset i + BAVC.deltaIndex delta i))
      (BAVC.hashLen * (BAVC.leafOffset i + BAVC.deltaIndex delta i) + BAVC.hashLen) with hf
  have hf32 : ∀ i < BAVC.tau, (f i).size = 32 := by
    intro i hi
    have hl := hidden_leaf_lt delta hi
    simp only [hf, ByteArray.size_extract]
    have : BAVC.hashLen * (BAVC.leafOffset i + BAVC.deltaIndex delta i) + BAVC.hashLen ≤
        coms.size := by
      rw [hcs, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hl
    simp only [BAVC.hashLen] at this ⊢; omega
  set H := (List.range BAVC.tau).foldl (fun acc i => acc ++ f i) ByteArray.empty with hH
  have hHL : H = ((List.range BAVC.tau).map f).foldl (· ++ ·) ByteArray.empty := by
    rw [hH, List.foldl_map]
  have hmapf : ∀ b ∈ (List.range BAVC.tau).map f, b.size = 32 := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
    exact hf32 i (List.mem_range.1 hi)
  have hHs : H.size = BAVC.tau * BAVC.hashLen := by
    rw [hHL, size_foldl_uniform 32 _ _ hmapf, List.length_map, List.length_range]; rfl
  set body := seeds.foldl (· ++ ·) H with hbody
  have hbodyL : body = seeds.toList.foldl (· ++ ·) H := by rw [hbody, Array.foldl_toList]
  have hbs : body.size = BAVC.tau * BAVC.hashLen + 16 * nodes.size := by
    rw [hbodyL, size_foldl_uniform 16 _ _ hseed16, hHs, Array.length_toList, hsz]
  have h105 : nodes.size ≤ 105 := by rw [← hsz]; exact Nat.le_of_not_gt hbig
  have hle : body.size ≤ BAVC.openSize := by
    have e1 : BAVC.openSize = 2224 := rfl
    have e2 : BAVC.tau * BAVC.hashLen = 544 := rfl
    rw [hbs, e1, e2]; omega
  refine ⟨?_, h105, ?_, ?_, ?_⟩
  · show (body ++ Prover.zeros _).size = _
    rw [ByteArray.size_append, zeros_size]; omega
  · intro i hi
    have hi32 : BAVC.hashLen * i + BAVC.hashLen ≤ H.size := by
      rw [hHs]; simp only [BAVC.hashLen, BAVC.tau] at hi ⊢; omega
    rw [extract_append_of_le _ _ (by omega), hbodyL, foldl_append_eq,
      extract_append_of_le _ _ hi32, hHL]
    have e := extract_foldl_uniform 32 _ ByteArray.empty hmapf i (by simpa using hi)
    simp only [ByteArray.size_empty, Nat.zero_add] at e
    rw [show BAVC.hashLen = 32 from rfl, e]
    simp only [List.getElem_map, List.getElem_range]
    rfl
  · intro k hk
    rw [extract_append_of_le _ _ (by rw [hbs]; omega), hbodyL, ← hHs]
    rw [extract_foldl_uniform 16 _ H hseed16 k (by simpa [hsz] using hk)]
    exact hseedL k _
  · intro q hq
    show (body ++ Prover.zeros _).get! q = 0
    rw [get!_append]
    simp only [show ¬ q < body.size by omega, ↓reduceIte]
    exact get!_zeros _ _

/-! ## The verifier's reconstruction -/

/-- The known seeds are the tree's nodes. -/
def Sound (seed iv : ByteArray) (A : Array (Option ByteArray)) : Prop :=
  A.size = BAVC.numNodes ∧ ∀ c x, A[c]! = some x → x = treeNode seed iv c

lemma getElem!_set!_some (A : Array (Option ByteArray)) (i c : ℕ) (v : ByteArray)
    (h : (A[c]!).isSome) : ((A.set! i (some v))[c]!).isSome := by
  rw [getElem!_set!]; split_ifs <;> simp_all

lemma Sound.set {seed iv : ByteArray} {A : Array (Option ByteArray)} (hA : Sound seed iv A) {i : ℕ}
    {v : ByteArray} (hv : v = treeNode seed iv i) : Sound seed iv (A.set! i (some v)) := by
  refine ⟨by rw [size_set!, hA.1], fun c x hx => ?_⟩
  rw [getElem!_set!] at hx
  split_ifs at hx with h
  · rw [← h.1, ← hv]; exact (Option.some.inj hx).symm
  · exact hA.2 c x hx

/-- **The placed seeds** are the tree's nodes at `openNodes Δ`. -/
theorem placed_spec (seed iv delta o : ByteArray)
    (hseed : ∀ k < (BAVC.openNodes delta).size,
      o.extract (BAVC.tau * BAVC.hashLen + 16 * k) (BAVC.tau * BAVC.hashLen + 16 * k + 16) =
        treeNode seed iv (BAVC.openNodes delta)[k]!) :
    let A := (List.range (BAVC.openNodes delta).size).foldl (fun known k =>
        known.set! (BAVC.openNodes delta)[k]! (some (o.extract (BAVC.tau * BAVC.hashLen + 16 * k)
          (BAVC.tau * BAVC.hashLen + 16 * k + 16))))
      (Array.replicate BAVC.numNodes none)
    Sound seed iv A ∧ ∀ c ∈ BAVC.openNodes delta, (A[c]!).isSome := by
  have hget := fun k (hk : k < (BAVC.openNodes delta).size) => (openNodes_get delta hk).2
  generalize BAVC.openNodes delta = nodes at *
  have key : ∀ N, N ≤ nodes.size →
      let A := (List.range N).foldl (fun known k =>
          known.set! nodes[k]! (some (o.extract (BAVC.tau * BAVC.hashLen + 16 * k)
            (BAVC.tau * BAVC.hashLen + 16 * k + 16))))
        (Array.replicate BAVC.numNodes none)
      Sound seed iv A ∧ ∀ k < N, (A[nodes[k]!]!).isSome := by
    intro N
    induction N with
    | zero =>
      intro _
      simp only [List.range_zero, List.foldl_nil]
      refine ⟨⟨by simp, fun c x hx => ?_⟩, fun k hk => absurd hk (by omega)⟩
      rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_replicate] at hx
      split_ifs at hx <;> simp at hx
    | succ N ih =>
      intro hN
      obtain ⟨h1, h2⟩ := ih (by omega)
      show _ ∧ _
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      refine ⟨h1.set (hseed N (by omega)), fun k hk => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact getElem!_set!_some _ _ _ _ (h2 k hk)
      · rw [getElem!_set!, h1.1]
        simp only [hget k (by omega), and_self, ↓reduceIte, Option.isSome_some]
  obtain ⟨h1, h2⟩ := key _ le_rfl
  refine ⟨h1, fun c hc => ?_⟩
  obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 hc
  rw [← getElem!_pos nodes k hk]
  exact h2 k hk

/-- **The top-down derivation** knows every node off the hidden paths. -/
theorem derive_spec (seed iv delta : ByteArray) (A : Array (Option ByteArray))
    (hA : Sound seed iv A) (hopen : ∀ c ∈ BAVC.openNodes delta, (A[c]!).isSome) :
    ∀ c < BAVC.numNodes, hid delta c = false →
      ((List.range (BAVC.numLeaves - 1)).foldl (BAVC.deriveStep iv) A)[c]! =
        some (treeNode seed iv c) := by
  have hL : BAVC.numLeaves - 1 = 2303 := rfl
  have hN : BAVC.numNodes = 4607 := rfl
  have key : ∀ N, N ≤ BAVC.numLeaves - 1 →
      let B := (List.range N).foldl (BAVC.deriveStep iv) A
      Sound seed iv B ∧ ∀ c < BAVC.numNodes, hid delta c = false →
        (c ∈ BAVC.openNodes delta ∨ (1 ≤ c ∧ (c - 1) / 2 < N)) → (B[c]!).isSome := by
    intro N
    induction N with
    | zero =>
      intro _
      simp only [List.range_zero, List.foldl_nil]
      refine ⟨hA, fun c _ _ h => ?_⟩
      rcases h with h | h
      · exact hopen c h
      · omega
    | succ N ih =>
      intro hN'
      obtain ⟨h1, h2⟩ := ih (by omega)
      show _ ∧ _
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set B := (List.range N).foldl (BAVC.deriveStep iv) A
      -- Node `N` is known if it is off the hidden paths.
      have hNk : hid delta N = false → (B[N]!).isSome := by
        intro hn
        have hpos : 1 ≤ N := by
          rcases Nat.eq_zero_or_pos N with rfl | h
          · rw [hid_root] at hn; exact absurd hn (by decide)
          · exact h
        exact h2 N (by omega) hn (Or.inr ⟨hpos, by omega⟩)
      unfold BAVC.deriveStep
      cases hB : B[N]! with
      | none =>
        refine ⟨h1, fun c hc hcn h => ?_⟩
        rcases h with h | ⟨hc1, hcN⟩
        · exact h2 c hc hcn (Or.inl h)
        rcases Nat.lt_succ_iff_lt_or_eq.1 hcN with hcN | hcN
        · exact h2 c hc hcn (Or.inr ⟨hc1, hcN⟩)
        · -- The parent `N` is on a hidden path, so `c` was opened.
          have hpar : hid delta N = true := by
            cases hh : hid delta N
            · have := hNk hh; rw [hB] at this; exact absurd this (by decide)
            · rfl
          exact h2 c hc hcn (Or.inl (mem_openNodes delta hc1 hc hcn (hcN ▸ hpar)))
      | some node =>
        have hnode : node = treeNode seed iv N := h1.2 N node hB
        subst hnode
        refine ⟨(h1.set (treeNode_left seed iv N).symm).set (treeNode_right seed iv N).symm,
          fun c hc hcn h => ?_⟩
        rcases h with h | ⟨hc1, hcN⟩
        · exact getElem!_set!_some _ _ _ _ (getElem!_set!_some _ _ _ _ (h2 c hc hcn (Or.inl h)))
        rcases Nat.lt_succ_iff_lt_or_eq.1 hcN with hcN | hcN
        · exact getElem!_set!_some _ _ _ _ (getElem!_set!_some _ _ _ _
            (h2 c hc hcn (Or.inr ⟨hc1, hcN⟩)))
        · have hs : ∀ (X : Array (Option ByteArray)) (v : ByteArray), X.size = BAVC.numNodes →
              ((X.set! c (some v))[c]!).isSome := by
            intro X v hX; rw [getElem!_set!]; simp [hX, hc]
          rcases Nat.even_or_odd c with ⟨q, hq⟩ | ⟨q, hq⟩
          · rw [show 2 * N + 2 = c by omega]
            exact hs _ _ (by rw [size_set!, h1.1])
          · rw [show 2 * N + 1 = c by omega]
            exact getElem!_set!_some _ _ _ _ (hs _ _ h1.1)
  intro c hc hcn
  obtain ⟨h1, h2⟩ := key _ le_rfl
  have hs := h2 c hc hcn (Or.inr ⟨?_, by omega⟩)
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hs
    rw [hx, h1.2 c x hx]
  · rcases Nat.eq_zero_or_pos c with rfl | h
    · rw [hid_root] at hcn; exact absurd hcn (by decide)
    · exact h

lemma lt_size_of_getElem!_some {α : Type} {A : Array (Option α)} {c : ℕ} {x : α}
    (h : A[c]! = some x) : c < A.size := by
  by_contra hc
  rw [getElem!_neg A c hc] at h
  exact absurd h (by simp [default])

/-! ## BAVC completeness -/

/-- **BAVC completeness** (`one_tree_bavc::open`, then `verify`): an opening of the prover's tree
at any `Δ` reconstructs the prover's leaf keys off the hidden leaves, and its commitments. -/
theorem bavcComplete : BAVCComplete := by
  intro seed iv delta o ho
  obtain ⟨hosz, h105, hhid, hseed, hzero⟩ := opening_spec seed iv delta o ho
  obtain ⟨hpl, hplo⟩ := placed_spec seed iv delta o hseed
  have hder := derive_spec seed iv delta _ hpl hplo
  rw [fit_of_size hosz]
  -- The commitment's pieces.
  have htree : ∀ k < BAVC.numNodes, (BAVC.commit seed iv).1[k]! = treeNode seed iv k :=
    fun k hk => expandTree_get seed iv hk
  have hcommit : (BAVC.commit seed iv).2 = BAVC.leavesOf iv (BAVC.commit seed iv).1
      (fun _ => none) (fun _ => ByteArray.empty) := rfl
  set tP := (BAVC.commit seed iv).1
  set derived := (List.range (BAVC.numLeaves - 1)).foldl (BAVC.deriveStep iv)
    ((List.range (BAVC.openNodes delta).size).foldl (fun known k =>
        known.set! (BAVC.openNodes delta)[k]! (some (o.extract (BAVC.tau * BAVC.hashLen + 16 * k)
          (BAVC.tau * BAVC.hashLen + 16 * k + 16))))
      (Array.replicate BAVC.numNodes none)) with hderived
  set tR := derived.map (·.getD BAVC.zeroBlock) with htR
  have htR_get : ∀ c < BAVC.numNodes, hid delta c = false → tR[c]! = treeNode seed iv c := by
    intro c hc hcn
    have h := hder c hc hcn
    rw [htR, getElem!_map' _ _ (lt_size_of_getElem!_some h), h]
    rfl
  -- The reconstruction accepts.
  have hcond : (o.size != BAVC.openSize ||
      decide (BAVC.tau * BAVC.hashLen + 16 * (BAVC.openNodes delta).size > BAVC.openSize) ||
      (List.range (BAVC.openSize - (BAVC.tau * BAVC.hashLen + 16 * (BAVC.openNodes delta).size))).any
        fun k => o.get! (BAVC.tau * BAVC.hashLen + 16 * (BAVC.openNodes delta).size + k) != 0) =
      false := by
    have e1 : BAVC.openSize = 2224 := rfl
    have e2 : BAVC.tau * BAVC.hashLen = 544 := rfl
    simp only [hosz, bne_self_eq_false, Bool.false_or, Bool.or_eq_false_iff, decide_eq_false_iff_not,
      List.any_eq_false, List.mem_range, bne_iff_ne, ne_eq, not_not]
    refine ⟨by rw [e1, e2]; omega, fun k _ => hzero _ (by omega)⟩
  have hrec : BAVC.reconstruct iv o delta = some (BAVC.leavesOf iv tR
      (fun i => some (BAVC.deltaIndex delta i))
      (fun i => o.extract (BAVC.hashLen * i) (BAVC.hashLen * i + BAVC.hashLen))) := by
    rw [BAVC.reconstruct]
    simp only []
    rw [hcond]
    rfl
  have hnone : ∀ j : ℕ, ((none : Option ℕ) == some j) = false := fun _ => rfl
  have hsome : ∀ a j : ℕ, (some a == some j) = decide (a = j) := fun a j => by
    by_cases h : a = j
    · subst h; simp
    · simp [h]
  have hpos : ∀ {i j}, 1 ≤ BAVC.treePos i j := fun {i j} => by
    have := treePos_ge i j; simp only [BAVC.numLeaves] at this; omega
  have hoff : ∀ {i j}, i < BAVC.tau → j < 2 ^ BAVC.kOf i → j ≠ BAVC.deltaIndex delta i →
      tR[BAVC.treePos i j]! = treeNode seed iv (BAVC.treePos i j) := fun hi hj hjd =>
    htR_get _ (treePos_lt hi hj) (by rw [hid_treePos delta hi hj]; exact decide_eq_false hjd)
  refine ⟨_, hrec, ?_, ?_⟩
  · -- The commitments.
    rw [hcommit, leavesOf_eq, leavesOf_eq]
    simp only [hnone, hsome, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]
    refine congrArg (fun L => List.foldl (· ++ ·) ByteArray.empty L)
      (pieces_congr fun i hi j hj => ?_)
    by_cases hjd : BAVC.deltaIndex delta i = j
    · subst hjd
      simp only [↓reduceIte]
      rw [hhid i hi, hcommit, leavesOf_eq]
      simp only [hnone, Bool.false_eq_true, ↓reduceIte]
      exact extract_pieces _ 32 (fun i _ j _ => leafCom_size _ _ _) hi hj
    · simp only [hjd, ↓reduceIte]
      rw [hoff hi hj (Ne.symm hjd), htree _ (treePos_lt hi hj)]
  · -- The leaf keys off the hidden leaves.
    intro i hi j hj hjd
    simp only [leafKey]
    rw [hcommit, leavesOf_eq, leavesOf_eq]
    simp only [hnone, hsome, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]
    rw [extract_pieces _ 16 (fun i' hi' j' hj' => by
        split
        · rfl
        · rename_i hne
          rw [hoff hi' hj' (Ne.symm hne)]
          exact treeNode_size _ _ hpos) hi hj,
      extract_pieces _ 16 (fun i' hi' j' hj' => by
        rw [htree _ (treePos_lt hi' hj')]
        exact treeNode_size _ _ hpos) hi hj]
    simp only [Ne.symm hjd, ↓reduceIte]
    rw [hoff hi hj hjd, htree _ (treePos_lt hi hj)]

end VoleMole.Verifier.Bridge
