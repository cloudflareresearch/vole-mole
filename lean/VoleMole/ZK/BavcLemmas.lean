import VoleMole.ZK.ByteLemmas
import VoleMole.Verifier.Bridge.CtrInput

/-!
# Sizes in the BAVC commitment, and the opening's seed positions

Facts about the executable BAVC (`Verifier/BAVC.lean`, `BAVC.openSeeds` in `Verifier/Prover.lean`)
that `ZK/TapeOf.lean` needs to read the real prover's opening as the tape's commitments and
seeds:

* `encrypt_size`, `prg_size`: an AES block is 16 bytes, the CTR PRG's output `16 n`;
* `expandTree_size`, `expandTree_get_size`: the GGM tree has `2L − 1` nodes of 16 bytes (for a
  16-byte seed);
* `commit_coms_size`: the leaf commitments are `32 L` bytes;
* `openSeeds_eq`: the opened seeds are the tree's nodes at positions `openPos Δ` that depend on `Δ`
  only (so `Sim.openCount` is their number, `openSeeds_size`), all below `2L − 1`.
-/

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith

/-! ## AES -/

lemma size_id_bind {α : Type} (m : Id α) (f : α → ByteArray) {n : ℕ} (h : ∀ a, (f a).size = n) :
    ((m >>= fun a => pure (f a) : Id ByteArray)).size = n := h _

lemma encrypt_size (rk pt : ByteArray) : (AES.encrypt rk pt).size = 16 := by
  unfold AES.encrypt
  simp only [Id.run]
  refine size_id_bind _ _ fun a => ?_
  rw [Bridge.size_pushLE32, Bridge.size_pushLE32, Bridge.size_pushLE32, Bridge.size_pushLE32]
  rfl

lemma prg_size (key iv : ByteArray) (t c : UInt32) (n : ℕ) : (AES.prg key iv t c n).size = 16 * n := by
  rw [AES.prg, prgExpanded_eq]
  have : ∀ (l : List ℕ) (o : ByteArray), (l.foldl (fun out j =>
      out ++ AES.encrypt (AES.expandKey key) (AES.ctrBlock iv (c + j.toUInt32) t)) o).size =
      o.size + 16 * l.length := by
    intro l; induction l with
    | nil => simp
    | cons j l ih =>
      intro o; rw [List.foldl_cons, ih, ByteArray.size_append, encrypt_size]
      simp only [List.length_cons]; ring
  rw [this]
  simp only [List.length_range]
  show (Array.emptyWithCapacity (16 * n)).size + 16 * n = 16 * n
  simp

lemma children_size (iv node : ByteArray) (n : ℕ) : (BAVC.children iv node n).size = 32 := by
  rw [BAVC.children, prg_size]

lemma block_size (b : ByteArray) (k : ℕ) (h : 16 * k + 16 ≤ b.size) : (BAVC.block b k).size = 16 := by
  rw [BAVC.block, ByteArray.size_extract]; omega

lemma leafCom_size (iv key : ByteArray) (i : ℕ) : (BAVC.leafCom iv key i).size = 32 := by
  rw [BAVC.leafCom, prg_size]

lemma zeroBlock_size : BAVC.zeroBlock.size = 16 := rfl

/-! ## The tree -/

lemma getElem!_set! {α : Type} [Inhabited α] (t : Array α) (i : ℕ) (x : α) (k : ℕ) :
    (t.set! i x)[k]! = if i = k ∧ k < t.size then x else t[k]! := by
  simp only [Array.set!_eq_setIfInBounds, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds]
  split_ifs with h1 h2 h2 <;> simp_all

lemma size_set! {α : Type} (t : Array α) (i : ℕ) (x : α) : (t.set! i x).size = t.size := by
  simp

/-- Every node of the prover's tree has 16 bytes. -/
theorem expandTree_spec (seed iv : ByteArray) (hs : seed.size = 16) :
    (BAVC.expandTree seed iv).size = BAVC.numNodes ∧
      ∀ k < BAVC.numNodes, ((BAVC.expandTree seed iv)[k]!).size = 16 := by
  unfold BAVC.expandTree
  rw [Id.run]
  simp only [bind_pure]
  rw [forIn_range_foldl _ _ _ (fun n (t : Array ByteArray) =>
    (t.set! (2 * n + 1) (BAVC.block (BAVC.children iv t[n]! n) 0)).set! (2 * n + 2)
      (BAVC.block (BAVC.children iv t[n]! n) 1)) fun _ _ => rfl]
  generalize BAVC.numNodes = N
  have key : ∀ (l : List ℕ) (t : Array ByteArray), t.size = N →
      (∀ k < N, (t[k]!).size = 16) →
      (l.foldl (fun t n => (t.set! (2 * n + 1) (BAVC.block (BAVC.children iv t[n]! n) 0)).set!
        (2 * n + 2) (BAVC.block (BAVC.children iv t[n]! n) 1)) t).size = N ∧
      ∀ k < N, ((l.foldl (fun t n => (t.set! (2 * n + 1)
        (BAVC.block (BAVC.children iv t[n]! n) 0)).set! (2 * n + 2)
        (BAVC.block (BAVC.children iv t[n]! n) 1)) t)[k]!).size = 16 := by
    intro l
    induction l with
    | nil => intro t h1 h2; exact ⟨h1, h2⟩
    | cons n l ih =>
      intro t h1 h2
      refine ih _ (by simp [h1]) fun k hk => ?_
      have hb0 := block_size (BAVC.children iv t[n]! n) 0 (by simp [children_size])
      have hb1 := block_size (BAVC.children iv t[n]! n) 1 (by simp [children_size])
      rw [getElem!_set!, getElem!_set!]
      split_ifs
      · exact hb1
      · exact hb0
      · exact h2 k hk
  refine key _ ((Array.replicate N BAVC.zeroBlock).set! 0 seed) (by simp) fun k hk => ?_
  rw [getElem!_set!]
  split_ifs with h
  · exact hs
  · rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    simp [hk, zeroBlock_size]

/-! ## The leaves -/

lemma leafOffset_tau : BAVC.leafOffset BAVC.tau = BAVC.numLeaves := by decide

lemma sum_eq_leafOffset : ∀ n, ∑ i ∈ Finset.range n, 2 ^ BAVC.kOf i = BAVC.leafOffset n
  | 0 => rfl
  | n + 1 => by
    rw [Finset.sum_range_succ, sum_eq_leafOffset n, BAVC.leafOffset, BAVC.leafOffset,
      List.range_succ, List.foldl_append]
    rfl

/-- The state a loop body yields. -/
def stepVal {β : Type} (x : Id (ForInStep β)) : β :=
  match (x : ForInStep β) with
  | .yield b => b
  | .done b => b

/-- A `for` loop over `[0, n)` that always yields and adds `c i` to a measure. -/
lemma forIn_range_measure {β : Type} (n : ℕ) (init : β) (f : ℕ → β → Id (ForInStep β))
    (μ : β → ℕ) (c : ℕ → ℕ) (h : ∀ i b, ∃ b', f i b = pure (.yield b') ∧ μ b' = μ b + c i) :
    μ (forIn [:n] init f : Id β) = μ init + ∑ i ∈ Finset.range n, c i := by
  have hf : ∀ i b, f i b = pure (.yield (stepVal (f i b))) := fun i b => by
    obtain ⟨b', hb', -⟩ := h i b
    rw [hb']; rfl
  have hμ : ∀ i b, μ (stepVal (f i b)) = μ b + c i := fun i b => by
    obtain ⟨b', hb', hm⟩ := h i b
    rw [hb']; exact hm
  rw [forIn_range_foldl n init f (fun i b => stepVal (f i b)) hf]
  show μ ((List.range n).foldl _ init) = _
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hμ, ih,
      Finset.sum_range_succ, Nat.add_assoc]

/-- The commitment's leaves: `32 L` bytes of commitments. -/
theorem commit_coms_size (seed iv : ByteArray) :
    (BAVC.commit seed iv).2.coms.size = BAVC.hashLen * BAVC.numLeaves := by
  simp only [BAVC.commit, BAVC.leavesOf]
  rw [Id.run]
  change (forIn (m := Id) [:BAVC.tau] (ByteArray.emptyWithCapacity (16 * BAVC.numLeaves),
    ByteArray.emptyWithCapacity (BAVC.hashLen * BAVC.numLeaves)) _).2.size = _
  rw [forIn_range_measure (μ := fun s : ByteArray × ByteArray => s.2.size)
    (c := fun i => BAVC.hashLen * 2 ^ BAVC.kOf i)]
  · have h0 : (ByteArray.emptyWithCapacity (BAVC.hashLen * BAVC.numLeaves)).size = 0 := by
      show (Array.emptyWithCapacity _).size = 0; simp
    rw [h0, Nat.zero_add, ← Finset.mul_sum, sum_eq_leafOffset, leafOffset_tau]
  · intro i b
    refine ⟨_, rfl, ?_⟩
    rw [forIn_range_measure (μ := fun s : ByteArray × ByteArray => s.2.size) (c := fun _ => 32)]
    · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, BAVC.hashLen]; ring
    · intro j s
      refine ⟨_, by simp; rfl, ?_⟩
      simp only [ByteArray.size_append, leafCom_size]

/-! ## The opened seeds -/

/-- The positions of the opened seeds (the walk of `BAVC.openSeeds`, recording positions). -/
def openPos (delta : ByteArray) : Array ℕ := Id.run do
  let mut hidden : Array Bool := Array.replicate BAVC.numNodes false
  for i in [0:BAVC.tau] do
    hidden := hidden.set! (BAVC.treePos i (BAVC.deltaIndex delta i)) true
  let mut pos : Array ℕ := #[]
  for m in [0:BAVC.numLeaves - 1] do
    let n := BAVC.numLeaves - 2 - m
    let l := hidden[2 * n + 1]!
    let r := hidden[2 * n + 2]!
    hidden := hidden.set! n (l || r)
    if l != r then pos := pos.push (if l then 2 * n + 2 else 2 * n + 1)
  return pos

/-- One step of the opening walk, recording the opened node with `rec`. -/
def walkStep {γ : Type} (rec : ℕ → γ) (m : ℕ) (x : Array Bool × Array γ) : Array Bool × Array γ :=
  if (x.1[2 * (BAVC.numLeaves - 2 - m) + 1]! != x.1[2 * (BAVC.numLeaves - 2 - m) + 2]!) = true then
    (x.1.set! (BAVC.numLeaves - 2 - m)
      (x.1[2 * (BAVC.numLeaves - 2 - m) + 1]! || x.1[2 * (BAVC.numLeaves - 2 - m) + 2]!),
     x.2.push (rec (if x.1[2 * (BAVC.numLeaves - 2 - m) + 1]! = true then
       2 * (BAVC.numLeaves - 2 - m) + 2 else 2 * (BAVC.numLeaves - 2 - m) + 1)))
  else
    (x.1.set! (BAVC.numLeaves - 2 - m)
      (x.1[2 * (BAVC.numLeaves - 2 - m) + 1]! || x.1[2 * (BAVC.numLeaves - 2 - m) + 2]!), x.2)

/-- The hidden-node marks before the walk. -/
def hiddenInit (delta : ByteArray) : Array Bool :=
  (List.range BAVC.tau).foldl (fun h i => h.set! (BAVC.treePos i (BAVC.deltaIndex delta i)) true)
    (Array.replicate BAVC.numNodes false)

lemma pure_id_eq {α : Type} (a : α) : (pure a : Id α) = a := rfl

lemma ite_pure_yield {β : Type} (c : Prop) [Decidable c] (a b : β) :
    (if c then (pure (.yield a) : Id (ForInStep β)) else pure (.yield b)) =
      pure (.yield (if c then a else b)) := by
  split <;> rfl

lemma openSeeds_walk (t : Array ByteArray) (delta : ByteArray) :
    BAVC.openSeeds t delta = ((List.range (BAVC.numLeaves - 1)).foldl
      (fun x m => walkStep (fun k => t[k]!) m x) (hiddenInit delta, #[])).2 := by
  unfold BAVC.openSeeds
  rw [Id.run]
  simp only [ite_pure_yield, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
    List.forIn_pure_yield_eq_foldl, bind_pure_comp, map_pure, walkStep, hiddenInit]
  exact pure_id_eq _

lemma openPos_walk (delta : ByteArray) :
    openPos delta = ((List.range (BAVC.numLeaves - 1)).foldl
      (fun x m => walkStep id m x) (hiddenInit delta, #[])).2 := by
  unfold openPos
  rw [Id.run]
  simp only [ite_pure_yield, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
    List.forIn_pure_yield_eq_foldl, bind_pure_comp, map_pure, walkStep, hiddenInit, id]
  exact pure_id_eq _

lemma walk_map {γ : Type} (g : ℕ → γ) : ∀ (l : List ℕ) (h : Array Bool) (q : Array ℕ),
    (l.foldl (fun x m => walkStep g m x) (h, q.map g)) =
      ((l.foldl (fun x m => walkStep id m x) (h, q)).1,
        (l.foldl (fun x m => walkStep id m x) (h, q)).2.map g)
  | [], _, _ => rfl
  | m :: l, h, q => by
    simp only [List.foldl_cons]
    unfold walkStep
    split
    · rw [← Array.map_push]; exact walk_map g l _ _
    · exact walk_map g l _ _

/-- **The opened seeds are the nodes at `openPos Δ`**. -/
theorem openSeeds_eq (t : Array ByteArray) (delta : ByteArray) :
    BAVC.openSeeds t delta = (openPos delta).map fun k => t[k]! := by
  have := walk_map (fun k => t[k]!) (List.range (BAVC.numLeaves - 1)) (hiddenInit delta) #[]
  rw [Array.map_empty] at this
  rw [openSeeds_walk, openPos_walk, this]

lemma walk_lt : ∀ (l : List ℕ) (h : Array Bool) (q : Array ℕ), (∀ m ∈ l, m < BAVC.numLeaves - 1) →
    (∀ k ∈ q, k < BAVC.numNodes) →
    ∀ k ∈ (l.foldl (fun x m => walkStep id m x) (h, q)).2, k < BAVC.numNodes
  | [], _, _, _, hq => hq
  | m :: l, h, q, hl, hq => by
    simp only [List.foldl_cons]
    have hm := hl m (by simp)
    unfold walkStep
    split
    · refine walk_lt l _ _ (fun m' hm' => hl m' (by simp [hm'])) fun k hk => ?_
      rw [Array.mem_push] at hk
      rcases hk with hk | rfl
      · exact hq k hk
      · have h1 : BAVC.numNodes = 2 * BAVC.numLeaves - 1 := rfl
        simp only [id, h1]; split <;> omega
    · exact walk_lt l _ _ (fun m' hm' => hl m' (by simp [hm'])) hq

theorem openPos_lt (delta : ByteArray) : ∀ k ∈ openPos delta, k < BAVC.numNodes := by
  rw [openPos_walk]
  exact walk_lt _ _ _ (fun m hm => List.mem_range.1 hm) (by simp)

/-- The number of opened seeds depends on `Δ` only. -/
theorem openSeeds_size (t : Array ByteArray) (delta : ByteArray) :
    (BAVC.openSeeds t delta).size = openCount delta := by
  rw [openCount, openSeeds_eq, openSeeds_eq, Array.size_map, Array.size_map]

end VoleMole.ZK.Sim
