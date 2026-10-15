import VoleMole.ZK.GrindNum
import VoleMole.Privacy.ZeroKnowledgeRO

/-!
# Zero knowledge with the tables visible, as `Privacy.ZeroKnowledgeRO`, and what the prover reads

`zk_rom_ic_h23_num` (`ZK/GrindNum.lean`) is stated for one proof and a distinguisher with explicit
read sets. The privacy games (`Privacy/MoussakaRO.lean`, `Privacy/RatatouilleRO.lean`) run several
proofs on the same tables, and their reductions run the other proofs themselves. Here:

* **The shared tables** `Sh p = Tab2G p × Tab5F × Cipher` (`H₂³` on every grinding point, `H₅` on
  every `37`-byte input, the cipher), and the private table of a proof: its `Tab3` (`H₃` at its own
  seed inputs `wPrefix ‖ μ₁ ‖ ρ ‖ 3`, a slice of `H₃` that depends on the proof's witness and
  instance).
* **Reads.** `Rd5 f q`, `RdE f q`: `f` reads the `H₅` table, the cipher, at most at `q` keys
  (adaptively: the key set may depend on the tables; outside it the tables can change without
  changing `f`). `Rd3`: the same for an `H₃` slice. `IsProg L q5 qE`: `L` only reprograms `H₂³`,
  reading `H₅` and the cipher at `q5`, `qE` keys. They compose (`Rd5.bind`, `Rd5.comp_prog`,
  `IsProg.comp`, …): a reduction that runs a real prover reads what the prover reads plus what the
  distinguisher reads.
* **The prover's reads** (`realRO`: the executable prover with the record `recH` and the
  ideal-cipher PRG `icPrg E`): the cipher at the `2L − 1 = 4607` nodes of its GGM tree
  (`realRO_rdE`; `voleGenAt_ic_congr`: the tree, the leaves' commitments, the small VOLEs, the
  sender columns and `u_hi` all read rows of the tree's nodes), `H₅` at its `2·312` gate inputs
  (`realRO_rd5`: `c_mult`'s two label hashes per gate).
* **The simulator's programming** (`progRO`: `simTab`, `H₂³` at the grinding points of the prefix
  recomputed from the simulated proof): `IsProg (progRO …) 312 4607` (`progRO_isProg`; the
  recomputation reads `H₅` at the verifier's gate inputs, `vIn5`, and the cipher at the
  reconstruction's nodes, `rdKeys`).
* **`zk_ro`**: `zk_rom_ic_h23_num` in this form, with error `εRO q₃ q₅ q_E =
  q₃·2⁻¹²⁸ + 2⁻¹¹⁰ + 221·(4607 + q_E + 4607)·2⁻¹²⁸ + (q₅ + 1)·2⁻¹²⁸`; `lean_zeroKnowledgeRO`: the
  Lean prover is `ZeroKnowledgeRO` for every relation whose statements have dedicated label rows,
  against the distinguishers with budgets `(q₃, q₅, q_E)` (`Budget`).
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy

/-! ## The shared tables and their reads -/

/-- **The tables the proofs of a game share**: `H₂³` on every grinding point of parameters `p`'s
prefix length, `H₅` on every `37`-byte input, the cipher. -/
abbrev Sh (p : Params) := Tab2G p × Tab5F × Cipher

section Reads

variable {p : Params} {X Y : Sort*}

/-- `f` reads the `H₅` table at most at `q` keys: outside `Q s` the table can change. -/
def Rd5 (f : Sh p → X) (q : ℕ) : Prop :=
  ∃ Q : Sh p → Finset (Bytes 37), (∀ s, (Q s).card ≤ q) ∧
    ∀ s (G5 : Tab5F), (∀ k ∈ Q s, s.2.1 k = G5 k) → f (s.1, G5, s.2.2) = f s

/-- `f` reads the cipher at most at `q` keys. -/
def RdE (f : Sh p → X) (q : ℕ) : Prop :=
  ∃ Q : Sh p → Finset Blk, (∀ s, (Q s).card ≤ q) ∧
    ∀ s (E : Cipher), (∀ k ∈ Q s, s.2.2 k = E k) → f (s.1, s.2.1, E) = f s

/-- `f` reads an `H₃` slice at most at `q` keys. -/
def Rd3 (f : Tab3 → X) (q : ℕ) : Prop :=
  ∃ Q : Tab3 → Finset (Bytes 16), (∀ g, (Q g).card ≤ q) ∧
    ∀ g g' : Tab3, (∀ k ∈ Q g, g k = g' k) → f g' = f g

/-- **A programming of `H₂³`**: `L` changes only the `H₂³` table, and the new table reads `H₅` and
the cipher at most at `q5`, `qE` keys. -/
def IsProg (L : Sh p → Sh p) (q5 qE : ℕ) : Prop :=
  (∀ s, (L s).2 = s.2) ∧ Rd5 (fun s => (L s).1) q5 ∧ RdE (fun s => (L s).1) qE

lemma Rd5.mono {f : Sh p → X} {q q' : ℕ} (h : Rd5 f q) (hq : q ≤ q') : Rd5 f q' := by
  obtain ⟨Q, hQ, hf⟩ := h
  exact ⟨Q, fun s => (hQ s).trans hq, hf⟩

lemma RdE.mono {f : Sh p → X} {q q' : ℕ} (h : RdE f q) (hq : q ≤ q') : RdE f q' := by
  obtain ⟨Q, hQ, hf⟩ := h
  exact ⟨Q, fun s => (hQ s).trans hq, hf⟩

lemma Rd3.mono {f : Tab3 → X} {q q' : ℕ} (h : Rd3 f q) (hq : q ≤ q') : Rd3 f q' := by
  obtain ⟨Q, hQ, hf⟩ := h
  exact ⟨Q, fun s => (hQ s).trans hq, hf⟩

lemma Rd5.const (x : X) : Rd5 (fun _ : Sh p => x) 0 :=
  ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩

lemma RdE.const (x : X) : RdE (fun _ : Sh p => x) 0 :=
  ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩

lemma Rd3.const (x : X) : Rd3 (fun _ : Tab3 => x) 0 :=
  ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩

/-- **Sequencing**: `f` run on `m`'s output reads what `m` reads and what `f` reads. -/
lemma Rd5.bind {m : Sh p → Y} {f : Y → Sh p → X} {a b : ℕ} (hm : Rd5 m a)
    (hf : ∀ y, Rd5 (f y) b) : Rd5 (fun s => f (m s) s) (a + b) := by
  classical
  obtain ⟨Qm, hQm, hm⟩ := hm
  choose Qf hQf hf using hf
  refine ⟨fun s => Qm s ∪ Qf (m s) s, fun s => (card_union_le _ _).trans (add_le_add (hQm s)
    (hQf _ s)), fun s G5 h => ?_⟩
  simp only
  rw [hm s G5 fun k hk => h k (mem_union_left _ hk)]
  exact hf (m s) s G5 fun k hk => h k (mem_union_right _ hk)

lemma RdE.bind {m : Sh p → Y} {f : Y → Sh p → X} {a b : ℕ} (hm : RdE m a)
    (hf : ∀ y, RdE (f y) b) : RdE (fun s => f (m s) s) (a + b) := by
  classical
  obtain ⟨Qm, hQm, hm⟩ := hm
  choose Qf hQf hf using hf
  refine ⟨fun s => Qm s ∪ Qf (m s) s, fun s => (card_union_le _ _).trans (add_le_add (hQm s)
    (hQf _ s)), fun s E h => ?_⟩
  simp only
  rw [hm s E fun k hk => h k (mem_union_left _ hk)]
  exact hf (m s) s E fun k hk => h k (mem_union_right _ hk)

lemma Rd3.bind {m : Tab3 → Y} {f : Y → Tab3 → X} {a b : ℕ} (hm : Rd3 m a)
    (hf : ∀ y, Rd3 (f y) b) : Rd3 (fun s => f (m s) s) (a + b) := by
  classical
  obtain ⟨Qm, hQm, hm⟩ := hm
  choose Qf hQf hf using hf
  refine ⟨fun s => Qm s ∪ Qf (m s) s, fun s => (card_union_le _ _).trans (add_le_add (hQm s)
    (hQf _ s)), fun s g h => ?_⟩
  simp only
  rw [hm s g fun k hk => h k (mem_union_left _ hk)]
  exact hf (m s) s g fun k hk => h k (mem_union_right _ hk)

lemma Rd5.map {m : Sh p → Y} {a : ℕ} (hm : Rd5 m a) (f : Y → X) : Rd5 (fun s => f (m s)) a := by
  simpa using hm.bind (f := fun y _ => f y) fun y => Rd5.const (f y)

lemma RdE.map {m : Sh p → Y} {a : ℕ} (hm : RdE m a) (f : Y → X) : RdE (fun s => f (m s)) a := by
  simpa using hm.bind (f := fun y _ => f y) fun y => RdE.const (f y)

lemma Rd3.map {m : Tab3 → Y} {a : ℕ} (hm : Rd3 m a) (f : Y → X) : Rd3 (fun s => f (m s)) a := by
  simpa using hm.bind (f := fun y _ => f y) fun y => Rd3.const (f y)

/-- **A reader after a programming** reads what it reads on the programmed tables and what the
programming reads. -/
lemma Rd5.comp_prog {f : Sh p → X} {L : Sh p → Sh p} {a b c : ℕ} (hf : Rd5 f a)
    (hL : IsProg L b c) : Rd5 (fun s => f (L s)) (a + b) := by
  classical
  obtain ⟨Qf, hQf, hf⟩ := hf
  obtain ⟨hL2, ⟨QL, hQL, hL1⟩, -⟩ := hL
  refine ⟨fun s => Qf (L s) ∪ QL s, fun s => (card_union_le _ _).trans (add_le_add (hQf _)
    (hQL s)), fun s G5 h => ?_⟩
  have e1 := hL1 s G5 fun k hk => h k (mem_union_right _ hk)
  have e2 := hL2 (s.1, G5, s.2.2)
  have e3 := hL2 s
  have hLs : L (s.1, G5, s.2.2) = ((L s).1, G5, (L s).2.2) := by
    refine Prod.ext e1 ?_
    rw [e2, e3]
  simp only
  rw [hLs]
  refine hf (L s) G5 fun k hk => ?_
  rw [e3]
  exact h k (mem_union_left _ hk)

lemma RdE.comp_prog {f : Sh p → X} {L : Sh p → Sh p} {a b c : ℕ} (hf : RdE f a)
    (hL : IsProg L b c) : RdE (fun s => f (L s)) (a + c) := by
  classical
  obtain ⟨Qf, hQf, hf⟩ := hf
  obtain ⟨hL2, -, ⟨QL, hQL, hL1⟩⟩ := hL
  refine ⟨fun s => Qf (L s) ∪ QL s, fun s => (card_union_le _ _).trans (add_le_add (hQf _)
    (hQL s)), fun s E h => ?_⟩
  have e1 := hL1 s E fun k hk => h k (mem_union_right _ hk)
  have e2 := hL2 (s.1, s.2.1, E)
  have e3 := hL2 s
  have hLs : L (s.1, s.2.1, E) = ((L s).1, (L s).2.1, E) := by
    refine Prod.ext e1 ?_
    rw [e2, e3]
  simp only
  rw [hLs]
  refine hf (L s) E fun k hk => ?_
  rw [e3]
  exact h k (mem_union_left _ hk)

lemma IsProg.id : IsProg (fun s : Sh p => s) 0 0 :=
  ⟨fun _ => rfl, ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩,
    ⟨fun _ => ∅, fun _ => le_rfl, fun _ _ _ => rfl⟩⟩

lemma IsProg.comp {L L' : Sh p → Sh p} {a b a' b' : ℕ} (h : IsProg L a b) (h' : IsProg L' a' b') :
    IsProg (fun s => L (L' s)) (a + a') (b + b') :=
  ⟨fun s => by rw [h.1, h'.1], h.2.1.comp_prog h', h.2.2.comp_prog h'⟩

lemma IsProg.mono {L : Sh p → Sh p} {a b a' b' : ℕ} (h : IsProg L a b) (ha : a ≤ a') (hb : b ≤ b') :
    IsProg L a' b' :=
  ⟨h.1, h.2.1.mono ha, h.2.2.mono hb⟩

/-- A programming chosen by a test that does not read the tables. -/
lemma IsProg.ite {L L' : Sh p → Sh p} {a b : ℕ} (c : Prop) [Decidable c] (h : IsProg L a b)
    (h' : IsProg L' a b) : IsProg (fun s => if c then L s else L' s) a b := by
  by_cases hc : c
  · simpa only [hc, ite_true] using h
  · simpa only [hc, ite_false] using h'

end Reads

/-! ## The prover reads the cipher at its tree's nodes -/

section ProverE

variable {E E' : Cipher} {seed iv : ByteArray}

/-- The cipher tables agree at the rows of the nodes of the GGM tree from `seed` (computed with
`E`). -/
def NodesAgree (E E' : Cipher) (seed iv : ByteArray) : Prop :=
  ∀ n < BAVC.numNodes, (@treeNode (icPrg E) seed iv n).size = 16 →
    E (blk 16 (@treeNode (icPrg E) seed iv n)) = E' (blk 16 (@treeNode (icPrg E) seed iv n))

/-- **The tree reads the cipher only at its nodes.** -/
theorem treeNode_ic_congr (h : NodesAgree E E' seed iv) :
    ∀ n < BAVC.numNodes, @treeNode (icPrg E) seed iv n = @treeNode (icPrg E') seed iv n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases n with _ | m
    · rw [@treeNode.eq_1 (icPrg E), @treeNode.eq_1 (icPrg E')]
    · rw [@treeNode.eq_2 (icPrg E), @treeNode.eq_2 (icPrg E'), ← ih (m / 2) (by omega) (by omega)]
      unfold BAVC.children
      rw [icPrg_congr (h (m / 2) (by omega))]

theorem expandTree_ic_congr (hs : seed.size = 16) (h : NodesAgree E E' seed iv) :
    @BAVC.expandTree (icPrg E) seed iv = @BAVC.expandTree (icPrg E') seed iv := by
  have s1 := (@expandTree_spec (icPrg E) seed iv hs).1
  have s2 := (@expandTree_spec (icPrg E') seed iv hs).1
  refine Array.ext (by rw [s1, s2]) fun i h1 h2 => ?_
  have hi : i < BAVC.numNodes := by rwa [s1] at h1
  rw [← getElem!_pos _ i h1, ← getElem!_pos _ i h2, @expandTree_get (icPrg E) _ _ _ hi,
    @expandTree_get (icPrg E') _ _ _ hi]
  exact treeNode_ic_congr h i hi

/-- **The commitment reads the cipher only at the tree's nodes.** -/
theorem commit_ic_congr (hs : seed.size = 16) (h : NodesAgree E E' seed iv) :
    @BAVC.commit (icPrg E) seed iv = @BAVC.commit (icPrg E') seed iv := by
  unfold BAVC.commit
  dsimp only
  rw [expandTree_ic_congr hs h, @leavesOf_eq (icPrg E), @leavesOf_eq (icPrg E')]
  simp only [Prod.mk.injEq, BAVC.Leaves.mk.injEq, true_and]
  apply congrArg (List.foldl (· ++ ·) ByteArray.empty)
  refine pieces_congr fun i hi j hj => ?_
  split_ifs
  · rfl
  · have hn := treePos_lt hi hj
    rw [@expandTree_get (icPrg E') _ _ _ hn, ← treeNode_ic_congr h _ hn]
    exact icPrg_congr (h _ hn) _ _ _ _

theorem smallVoleUWords_ic_congr (p : Params) (iv : ByteArray) (i : ℕ) (key : ℕ → ByteArray)
    (h : ∀ j < 2 ^ BAVC.kOf i, (key j).size = 16 → E (blk 16 (key j)) = E' (blk 16 (key j))) :
    @Prover.smallVoleUWords (icPrg E) p iv i key = @Prover.smallVoleUWords (icPrg E') p iv i key := by
  unfold Prover.smallVoleUWords
  refine List.foldl_ext _ _ _ fun acc j hj => ?_
  simp only [prgWords]
  rw [icPrg_congr (h j (List.mem_range.1 hj))]

theorem uMaskOf_ic_congr (p : Params) (T : CrtTables) (us : Array (Array UInt64))
    (h : seed.size = 16 → E (blk 16 seed) = E' (blk 16 seed)) :
    @Prover.uMaskOf (icPrg E) p T seed iv us = @Prover.uMaskOf (icPrg E') p T seed iv us := by
  unfold Prover.uMaskOf
  rw [icPrg_congr h]

/-- **Step 1 reads the cipher only at the tree's nodes** (the commitment, the small VOLEs' inputs
and the sender columns at the leaves, `u_hi` at the root). -/
theorem voleGenAt_ic_congr (Hs : Hashes) (T : CrtTables) (p : Params)
    (mu1 wPrefix ivPre binder1 : ByteArray) (hs : seed.size = 16)
    (h : NodesAgree E E' seed (Hs.hash .h4 ((ivPre ++ mu1).push 4))) :
    @voleGenAt (icPrg E) Hs T p mu1 wPrefix seed ivPre binder1 =
      @voleGenAt (icPrg E') Hs T p mu1 wPrefix seed ivPre binder1 := by
  set iv := Hs.hash .h4 ((ivPre ++ mu1).push 4) with hiv
  have hc := commit_ic_congr hs h
  have hk : ∀ i j, i < BAVC.tau → j < 2 ^ BAVC.kOf i →
      leafKey (@BAVC.commit (icPrg E') seed iv).2 i j = @treeNode (icPrg E) seed iv (BAVC.treePos i j) :=
    fun i j hi hj => by
      rw [@leafKey_commit (icPrg E') seed iv hs i j hi hj, treeNode_ic_congr h _ (treePos_lt hi hj)]
  have hus : (Array.range BAVC.tau).map (fun i =>
      @Prover.smallVoleUWords (icPrg E) p iv i (leafKey (@BAVC.commit (icPrg E') seed iv).2 i)) =
      (Array.range BAVC.tau).map (fun i =>
        @Prover.smallVoleUWords (icPrg E') p iv i (leafKey (@BAVC.commit (icPrg E') seed iv).2 i)) :=
    Array.map_congr_left fun i hi => smallVoleUWords_ic_congr _ _ _ _ fun j hj hsz => by
      have hi' := Array.mem_range.1 hi
      rw [hk i j hi' hj] at hsz ⊢
      exact h _ (treePos_lt hi' hj) hsz
  have hcols : @Prover.senderColumns (icPrg E) p iv (leafKey (@BAVC.commit (icPrg E') seed iv).2) =
      @Prover.senderColumns (icPrg E') p iv (leafKey (@BAVC.commit (icPrg E') seed iv).2) := by
    unfold Prover.senderColumns
    refine convertToVoleAt_ic_congr _ _ _ _ _ fun i hi j hj _ hsz => ?_
    rw [hk i j hi hj] at hsz ⊢
    exact h _ (treePos_lt hi hj) hsz
  have hum : ∀ us, @Prover.uMaskOf (icPrg E) p T seed iv us =
      @Prover.uMaskOf (icPrg E') p T seed iv us := fun us =>
    uMaskOf_ic_congr p T us fun hsz => by
      have := h 0 (by decide)
      rw [@treeNode.eq_1 (icPrg E)] at this
      exact this hsz
  simp only [voleGenAt, ← hiv, hc, hus, hcols, hum]

end ProverE

/-! ## The real prover and the programming, on the shared tables -/

section Real

variable (p : Params) (Hb : Hashes) (st : Statement) (w : ByteArray)

/-- **The record of the random-oracle model**, for `H₂³` tables of parameters `p` (`recH` at
`p = st.params`). -/
noncomputable def recHp (G3 : Tab3) (G2 : Tab2G p) (G5 : Tab5F) : Hashes :=
  ((Hb.withTable .h3 (seedInput (st.mu1 Hb) (w.extract 0 st.params.witnessBytes)) G3).withTable
    .h23 (enc2 p) G2).withTable .h5 enc5 G5

lemma recHp_eq : recHp st.params Hb st w = recH Hb st w := rfl

/-- **The real prover in the random-oracle and ideal-cipher model**: the executable prover with
randomness `ρ`, the record `recHp` (its `H₃` slice `G3`, the shared `H₂³` and `H₅` tables) and
the ideal-cipher PRG of the shared cipher table. -/
noncomputable def realROb (rho : ByteArray) (G3 : Tab3) (s : Sh p) : Except String ByteArray :=
  @Prover.prove (icPrg s.2.2) (recHp p Hb st w G3 s.1 s.2.1) CrtGen.tables st w rho
    st.params.witnessBytes

/-- `realROb` with a uniform 16-byte randomness `ρ`. -/
noncomputable def realRO (ρ : Bytes 16) (G3 : Tab3) (s : Sh p) : Except String ByteArray :=
  realROb p Hb st w (ba ρ) G3 s

/-- **The simulator's programming**: `H₂³` programmed at the grinding points of the prefix
recomputed from the simulated proof (`simTab`), answered by the coins' grinding answers. -/
noncomputable def progRO (c : SimCoins p) (s : Sh p) : Sh p :=
  (programAt (key2 p (@outPre (icPrg s.2.2) Hb CrtGen.tables st s.2.1 (simulate p c))) c.1.2.1 s.1,
    s.2)

lemma progRO_eq (c : SimCoins st.params) (s : Sh st.params) :
    progRO st.params Hb st c s =
      (@simTab (icPrg s.2.2) Hb CrtGen.tables st s.2.1 (simulate st.params c) c.1.2.1 s.1, s.2) :=
  rfl

end Real

section RealReads

variable {p : Params} {Hb : Hashes} {st : Statement} {w : ByteArray}

lemma recHp_h3 (G3 : Tab3) (G2 : Tab2G p) (G5 : Tab5F) :
    (recHp p Hb st w G3 G2 G5).hash .h3 =
      (Hb.withTable .h3 (seedInput (st.mu1 Hb) (w.extract 0 st.params.witnessBytes)) G3).hash .h3 := by
  funext x
  simp only [recHp, Hashes.withTable, reduceCtorEq, ite_false]

lemma recHp_h4 (G3 : Tab3) (G2 : Tab2G p) (G5 : Tab5F) :
    (recHp p Hb st w G3 G2 G5).hash .h4 = Hb.hash .h4 := by
  funext x
  simp only [recHp, Hashes.withTable, reduceCtorEq, ite_false]

lemma recHp_mu1 (G3 : Tab3) (G2 : Tab2G p) (G5 : Tab5F) :
    st.mu1 (recHp p Hb st w G3 G2 G5) = st.mu1 Hb := by
  have h1 : (recHp p Hb st w G3 G2 G5).hash .mu = Hb.hash .mu := by
    funext x; simp only [recHp, Hashes.withTable, reduceCtorEq, ite_false]
  have h2 : (recHp p Hb st w G3 G2 G5).hash .muDelayed = Hb.hash .muDelayed := by
    funext x; simp only [recHp, Hashes.withTable, reduceCtorEq, ite_false]
  simp only [Statement.mu1, VoleMole.Verifier.mu, h1, h2]

lemma recHp_wf (hHb : HashesWF Hb) (G3 : Tab3) (G2 : Tab2G p) (G5 : Tab5F) :
    HashesWF (recHp p Hb st w G3 G2 G5) :=
  ((hHb.withTable .h3 _ G3).withTable .h23 _ G2).withTable .h5 _ G5

/-- The prover's root seed from the record `Hs` and the randomness `rho`. -/
def rSeed (Hs : Hashes) (st : Statement) (w : ByteArray) (rho : ByteArray) : ByteArray :=
  (Hs.hash .h3 ((w.extract 0 st.params.witnessBytes ++ st.mu1 Hs ++ rho).push 3)).extract 0 16

/-- The prover's tree iv from the record `Hs` and the randomness `rho`. -/
def rIv (Hs : Hashes) (st : Statement) (w : ByteArray) (rho : ByteArray) : ByteArray :=
  Hs.hash .h4 (((Hs.hash .h3 ((w.extract 0 st.params.witnessBytes ++ st.mu1 Hs ++ rho).push 3)).extract
    16 32 ++ st.mu1 Hs).push 4)

/-- **The cipher keys the real prover reads**: the rows of its tree's `2L − 1` nodes. -/
noncomputable def realKeysE (p : Params) (Hb : Hashes) (st : Statement) (w : ByteArray)
    (rho : ByteArray) (G3 : Tab3) (s : Sh p) : Finset Blk :=
  (range BAVC.numNodes).image fun n => blk 16 (@treeNode (icPrg s.2.2)
    (rSeed (recHp p Hb st w G3 s.1 s.2.1) st w rho) (rIv (recHp p Hb st w G3 s.1 s.2.1) st w rho) n)

/-- **The real prover reads the cipher at most at `4607` keys** (the nodes of its tree). -/
theorem realROb_rdE (hHb : HashesWF Hb) (rho : ByteArray) (G3 : Tab3) :
    RdE (realROb p Hb st w rho G3) 4607 := by
  refine ⟨realKeysE p Hb st w rho G3, fun s => card_image_le.trans (le_of_eq (by
    rw [card_range]; rfl)), fun s E h => ?_⟩
  have hs : (rSeed (recHp p Hb st w G3 s.1 s.2.1) st w rho).size = 16 := by
    rw [rSeed, ByteArray.size_extract, recHp_wf hHb]; rfl
  unfold realROb Prover.prove
  dsimp only
  rw [@voleGen_eq_voleGenAt (icPrg E), @voleGen_eq_voleGenAt (icPrg s.2.2)]
  refine congrArg _ (voleGenAt_ic_congr _ _ _ _ _ _ _ hs fun n hn _ => ?_).symm
  exact h _ (mem_image.2 ⟨n, mem_range.2 hn, rfl⟩)

theorem realRO_rdE (hHb : HashesWF Hb) (ρ : Bytes 16) (G3 : Tab3) :
    RdE (realRO p Hb st w ρ G3) 4607 :=
  realROb_rdE hHb (ba ρ) G3

end RealReads

/-! ## The prover reads `H₅` at its gate inputs -/

section ProverH5

variable [HasPrg]

/-- `voleGenAt` with the two lists of gate hashes `h0`, `h1` given. -/
def vgH (Hs : Hashes) (T : CrtTables) (p : Params) (mu1 wPrefix seed ivPre binder1 : ByteArray)
    (h0 h1 : Array UInt32) : Prover.Pending :=
  let iv := Hs.hash .h4 ((ivPre ++ mu1).push 4)
  let tl := BAVC.commit seed iv
  let tree := tl.1
  let leaves := tl.2
  let check := BAVC.check (Hs.hash .h1) leaves.coms
  let key := leafKey leaves
  let us : Array (Array UInt64) :=
    (Array.range BAVC.tau).map fun i => Prover.smallVoleUWords p iv i (key i)
  let u := us[0]!
  let cols := Prover.senderColumns p iv key
  let corrections := (List.range (BAVC.tau - 1)).foldl
    (fun acc i => acc ++ Prover.correctionOf p u us[i + 1]!) ByteArray.empty
  let vOut := crtReconstructWith h0 p (fun _ => false) ByteArray.empty T cols
  let uMask := Prover.uMaskOf p T seed iv us
  let cmult := Prover.cMultOf p h0 h1 uMask
  let f0 : Prover.Fields :=
    { corrections := corrections, cmult := cmult, voleCheck := .empty, correction := .empty,
      qsProof := .empty, opening := .empty, delta := .empty, ivPre := ivPre, ctr := .empty }
  let c1 := chal1 Hs { params := p, bytes := Prover.assemble p f0 } mu1 check binder1
  let uRows : Array W128 := (Array.range p.correctionRows).map fun r =>
    if wbit u r then ⟨1, 0⟩ else W128.zero
  let uTilde := voleHashReceiver p c1 uRows uMask 0 (Prover.zeros 64)
  let hV := voleHashReceiver p c1 vOut.rows vOut.qMask 0 (Prover.zeros 64)
  let voleCheck := Prover.gfsToBytes uTilde
  let ub := bytesOfWords u
  let correction : ByteArray :=
    ⟨(Array.range wPrefix.size).map fun k => ub.get! k ^^^ wPrefix.get! k⟩
  { params := p, seed := seed, iv := iv, ivPre := ivPre, tree := tree, leaves := leaves, u := u,
    vRows := vOut.rows, vMask := vOut.qMask, uMask := uMask, chal1 := c1, hV := hV,
    wPrefix := wPrefix, fields := { f0 with voleCheck := voleCheck, correction := correction } }

/-- Step 1's tree iv. -/
def vgIv (Hs : Hashes) (mu1 ivPre : ByteArray) : ByteArray := Hs.hash .h4 ((ivPre ++ mu1).push 4)

/-- Step 1's sender columns. -/
def vgCols (Hs : Hashes) (p : Params) (mu1 seed ivPre : ByteArray) : Array (Array UInt64) :=
  Prover.senderColumns p (vgIv Hs mu1 ivPre) (leafKey (BAVC.commit seed (vgIv Hs mu1 ivPre)).2)

/-- Step 1's `u_pre` (the label-row offset). -/
def vgUPre (Hs : Hashes) (p : Params) (mu1 seed ivPre : ByteArray) : W128 :=
  let u := ((Array.range BAVC.tau).map fun i => Prover.smallVoleUWords p (vgIv Hs mu1 ivPre) i
    (leafKey (BAVC.commit seed (vgIv Hs mu1 ivPre)).2 i))[0]!
  ⟨wordAt u p.labelRowOffset, wordAt u (p.labelRowOffset + 64)⟩

/-- **Step 1's `H₅` inputs**: the gate inputs with both labels (`2·312`). -/
def vgIn5 (Hs : Hashes) (T : CrtTables) (p : Params) (mu1 seed ivPre : ByteArray) : List ByteArray :=
  Prover.gateInputsOff p T (vgIv Hs mu1 ivPre) (vgCols Hs p mu1 seed ivPre) W128.zero ++
    Prover.gateInputsOff p T (vgIv Hs mu1 ivPre) (vgCols Hs p mu1 seed ivPre)
      (vgUPre Hs p mu1 seed ivPre)

lemma vgIn5_length (Hs : Hashes) (T : CrtTables) (p : Params) (mu1 seed ivPre : ByteArray) :
    (vgIn5 Hs T p mu1 seed ivPre).length = 624 := by
  simp only [vgIn5, Prover.gateInputsOff, List.length_append, List.length_map, List.length_range,
    Params.nMult]

lemma voleGenAt_eq_vgH (Hs : Hashes) (T : CrtTables) (p : Params)
    (mu1 wPrefix seed ivPre binder1 : ByteArray) :
    voleGenAt Hs T p mu1 wPrefix seed ivPre binder1 = vgH Hs T p mu1 wPrefix seed ivPre binder1
      (gateWords ((Prover.gateInputsOff p T (vgIv Hs mu1 ivPre) (vgCols Hs p mu1 seed ivPre)
        W128.zero).map (Hs.hash .h5)))
      (gateWords ((Prover.gateInputsOff p T (vgIv Hs mu1 ivPre) (vgCols Hs p mu1 seed ivPre)
        (vgUPre Hs p mu1 seed ivPre)).map (Hs.hash .h5))) := rfl

variable {Hs Hs' : Hashes}

lemma vgH_agreeOff (h : Hs.AgreeOff .h5 Hs') (T : CrtTables) (p : Params)
    (mu1 wPrefix seed ivPre binder1 : ByteArray) (h0 h1 : Array UInt32) :
    vgH Hs T p mu1 wPrefix seed ivPre binder1 h0 h1 =
      vgH Hs' T p mu1 wPrefix seed ivPre binder1 h0 h1 := by
  simp only [vgH, h .h4 (by decide), h .h1 (by decide), h.chal1 (by decide)]

omit [HasPrg] in
lemma vgIv_agreeOff (h : Hs.AgreeOff .h5 Hs') (mu1 ivPre : ByteArray) :
    vgIv Hs mu1 ivPre = vgIv Hs' mu1 ivPre := by
  simp only [vgIv, h .h4 (by decide)]

lemma vgIn5_agreeOff (h : Hs.AgreeOff .h5 Hs') (T : CrtTables) (p : Params) (mu1 seed ivPre : ByteArray) :
    vgIn5 Hs T p mu1 seed ivPre = vgIn5 Hs' T p mu1 seed ivPre := by
  simp only [vgIn5, vgCols, vgUPre, vgIv_agreeOff h]

/-- **Step 1 reads `H₅` only at its gate inputs.** -/
theorem voleGenAt_h5_congr (h : Hs.AgreeOff .h5 Hs') (T : CrtTables) (p : Params)
    (mu1 wPrefix seed ivPre binder1 : ByteArray)
    (h5 : ∀ x ∈ vgIn5 Hs T p mu1 seed ivPre, Hs.hash .h5 x = Hs'.hash .h5 x) :
    voleGenAt Hs T p mu1 wPrefix seed ivPre binder1 =
      voleGenAt Hs' T p mu1 wPrefix seed ivPre binder1 := by
  rw [voleGenAt_eq_vgH, voleGenAt_eq_vgH, vgH_agreeOff h]
  have hc : vgCols Hs p mu1 seed ivPre = vgCols Hs' p mu1 seed ivPre := by
    simp only [vgCols, vgIv_agreeOff h]
  have hu : vgUPre Hs p mu1 seed ivPre = vgUPre Hs' p mu1 seed ivPre := by
    simp only [vgUPre, vgIv_agreeOff h]
  rw [← vgIv_agreeOff h, ← hc, ← hu]
  congr 2
  · exact List.map_congr_left fun x hx => h5 x (List.mem_append_left _ hx)
  · exact List.map_congr_left fun x hx => h5 x (List.mem_append_right _ hx)

omit [HasPrg] in
/-- **Step 2 does not read `H₅`.** -/
theorem proveCommit_agreeOff_h5 (h : Hs.AgreeOff .h5 Hs') (st : Statement) (suf : ByteArray)
    (P : Prover.Pending) : Prover.proveCommit Hs st suf P = Prover.proveCommit Hs' st suf P := by
  have e4 : Prover.grindStep Hs = Prover.grindStep Hs' := by
    funext s pre ctr
    simp only [Prover.grindStep, h .h23 (by decide)]
  simp only [Prover.proveCommit, h.chal2 (by decide), h.muDelayed (by decide) st,
    h.combBytes (fun _ => nofun) st, e4]

omit [HasPrg] in
/-- With `H₅` a table on the `37`-byte inputs, two tables that agree at an input's key answer it
alike. -/
lemma withTable_h5_congr (X : Hashes) {G5 G5' : Tab5F} {x : ByteArray}
    (h : x.size = 37 → G5 (blk 37 x) = G5' (blk 37 x)) :
    (X.withTable .h5 enc5 G5).hash .h5 x = (X.withTable .h5 enc5 G5').hash .h5 x := by
  simp only [Hashes.withTable, ite_true]
  split_ifs with hx
  · have hc : hx.choose = blk 37 x :=
      (blk_ba hx.choose).symm.trans (congrArg (blk 37) hx.choose_spec)
    have hs : x.size = 37 := by
      obtain ⟨a, ha⟩ := hx
      rw [← ha, enc5, size_ba]
    rw [hc, h hs]
  · rfl

end ProverH5

section RealReads5

variable {p : Params} {Hb : Hashes} {st : Statement} {w : ByteArray}

lemma recHp_agreeOff_h5 (G3 : Tab3) (G2 : Tab2G p) (G5 G5' : Tab5F) :
    (recHp p Hb st w G3 G2 G5).AgreeOff .h5 (recHp p Hb st w G3 G2 G5') := by
  intro k hk
  funext x
  simp only [recHp, Hashes.withTable, hk, ite_false]

/-- **The `H₅` keys the real prover reads**: its `2·312` gate inputs. -/
noncomputable def realKeys5 (p : Params) (Hb : Hashes) (st : Statement) (w : ByteArray)
    (rho : ByteArray) (G3 : Tab3) (s : Sh p) : Finset (Bytes 37) :=
  ((@vgIn5 (icPrg s.2.2) (recHp p Hb st w G3 s.1 s.2.1) CrtGen.tables st.params (st.mu1 Hb)
    (rSeed (recHp p Hb st w G3 s.1 s.2.1) st w rho)
    (((recHp p Hb st w G3 s.1 s.2.1).hash .h3 ((w.extract 0 st.params.witnessBytes ++ st.mu1 Hb ++
      rho).push 3)).extract 16 32)).toFinset).image (blk 37)

/-- **The real prover reads `H₅` at most at `624` keys** (its gate inputs, both labels). -/
theorem realROb_rd5 (rho : ByteArray) (G3 : Tab3) : Rd5 (realROb p Hb st w rho G3) 624 := by
  classical
  refine ⟨realKeys5 p Hb st w rho G3, fun s => ?_, fun s G5 h => ?_⟩
  · refine card_image_le.trans ((List.toFinset_card_le _).trans (le_of_eq ?_))
    exact @vgIn5_length (icPrg s.2.2) _ _ _ _ _ _
  have hA := recHp_agreeOff_h5 (Hb := Hb) (st := st) (w := w) G3 s.1 G5 s.2.1
  unfold realROb Prover.prove
  dsimp only
  rw [@voleGen_eq_voleGenAt (icPrg s.2.2), @voleGen_eq_voleGenAt (icPrg s.2.2),
    proveCommit_agreeOff_h5 hA, recHp_mu1, recHp_mu1, recHp_h3, recHp_h3]
  refine congrArg _ (@voleGenAt_h5_congr (icPrg s.2.2) _ _ hA _ _ _ _ _ _ _ fun x hx => ?_)
  rw [@vgIn5_agreeOff (icPrg s.2.2) _ _ hA] at hx
  refine withTable_h5_congr _ fun hs => (h _ (mem_image.2 ⟨x, ?_, rfl⟩)).symm
  rw [List.mem_toFinset]
  simpa only [realKeys5, rSeed, recHp_mu1, recHp_h3] using hx

theorem realRO_rd5 (ρ : Bytes 16) (G3 : Tab3) : Rd5 (realRO p Hb st w ρ G3) 624 :=
  realROb_rd5 (ba ρ) G3

end RealReads5

lemma rec5_agree_ne {Hb : Hashes} {G5 : Tab5F} {k : Kind} (hk : k ≠ .h5) :
    (rec5 Hb G5).hash k = Hb.hash k :=
  ((Hb.agreeOff_withTable .h5 enc5 G5) k hk).symm

/-! ## The programming reads the verifier's recomputation's keys -/

section ProgReads

variable {p : Params} {Hb : Hashes} {st : Statement}

/-- The `H₅` keys the recomputation of a proof's grinding prefix reads (the verifier's gate
inputs, at most `312`). -/
noncomputable def progKeys5 (Hb : Hashes) (st : Statement) (o : Except String ByteArray) (s : Sh p) :
    Finset (Bytes 37) :=
  match o with
  | .ok b => ((@vIn5 (icPrg s.2.2) (rec5 Hb s.2.1) CrtGen.tables st b).toFinset).image (blk 37)
  | .error _ => ∅

/-- The cipher keys the recomputation reads (the reconstruction's nodes, at most `4607`). -/
noncomputable def progKeysE (Hb : Hashes) (st : Statement) (o : Except String ByteArray) (s : Sh p) :
    Finset Blk :=
  match o with
  | .ok b => rdKeys s.2.2 (ivOf (rec5 Hb s.2.1) ⟨st.params, b⟩ (st.mu1 (rec5 Hb s.2.1)))
      (⟨st.params, b⟩ : Proof).opening (⟨st.params, b⟩ : Proof).delta
  | .error _ => ∅

/-- **The programming reads `H₅` at `312` and the cipher at `4607` keys.** -/
theorem progRO_isProg (c : SimCoins p) : IsProg (progRO p Hb st c) 312 4607 := by
  classical
  refine ⟨fun _ => rfl, ⟨progKeys5 Hb st (simulate p c), fun s => ?_, fun s G5 h => ?_⟩,
    ⟨progKeysE Hb st (simulate p c), fun s => ?_, fun s E h => ?_⟩⟩
  · unfold progKeys5
    split
    · exact card_image_le.trans ((List.toFinset_card_le _).trans
        (@vIn5_length_le (icPrg s.2.2) _ _ _ _))
    · simp
  · suffices e : @outPre (icPrg s.2.2) Hb CrtGen.tables st G5 (simulate p c) =
        @outPre (icPrg s.2.2) Hb CrtGen.tables st s.2.1 (simulate p c) by
      simp only [progRO, e]
    unfold progKeys5 at h
    unfold outPre
    split
    · rename_i b hb
      rw [hb] at h
      have hmu : st.mu1 (rec5 Hb G5) = st.mu1 (rec5 Hb s.2.1) := by rw [rec5_mu1, rec5_mu1]
      have h4 : (rec5 Hb G5).hash .h4 = (rec5 Hb s.2.1).hash .h4 := by rw [rec5_h4, rec5_h4]
      have hA : (rec5 Hb G5).AgreeOff .h5 (rec5 Hb s.2.1) := by
        intro k hk; rw [rec5_agree_ne hk, rec5_agree_ne hk]
      refine @vPre_h5_congr (icPrg s.2.2) _ _ hA _ _ _ fun x hx => ?_
      rw [@vIn5_congr (icPrg s.2.2) _ st _ _ hmu h4] at hx
      refine withTable_h5_congr _ fun _ => (h _ (mem_image.2 ⟨x, List.mem_toFinset.2 hx, rfl⟩)).symm
    · rfl
  · unfold progKeysE
    split
    · exact rdKeys_card _ _ _ _
    · simp
  · suffices e : @outPre (icPrg E) Hb CrtGen.tables st s.2.1 (simulate p c) =
        @outPre (icPrg s.2.2) Hb CrtGen.tables st s.2.1 (simulate p c) by
      simp only [progRO, e]
    unfold progKeysE at h
    unfold outPre
    split
    · rename_i b hb
      rw [hb] at h
      exact (vPre_ic_congr _ _ _ _ h).symm
    · rfl

end ProgReads

/-! ## Zero knowledge with the tables visible -/

section ZKRO

/-- **The error of `zk_rom_ic_h23_num`** at budgets `q₃`, `q₅`, `q_E`. -/
noncomputable def εRO (q3 q5 qE : ℕ) : ℝ :=
  q3 / 2 ^ 128 + 1 / 2 ^ 110 + 221 * (4607 + (qE + 4607)) / 2 ^ 128 + (q5 + 1) / 2 ^ 128

lemma εRO_mono {q3 q5 qE q3' q5' qE' : ℕ} (h3 : q3 ≤ q3') (h5 : q5 ≤ q5') (hE : qE ≤ qE') :
    εRO q3 q5 qE ≤ εRO q3' q5' qE' := by
  unfold εRO
  have h3' : (q3 : ℝ) ≤ q3' := by exact_mod_cast h3
  have h5' : (q5 : ℝ) ≤ q5' := by exact_mod_cast h5
  have hE' : (qE : ℝ) ≤ qE' := by exact_mod_cast hE
  gcongr

lemma εRO_nonneg' (q3 q5 qE : ℕ) : 0 ≤ εRO q3 q5 qE := by unfold εRO; positivity

/-- **The budget of a distinguisher** that sees an output, an `H₃` slice and the shared tables:
it reads the slice at `q3`, `H₅` at `q5` and the cipher at `qE` keys (each with the rest fixed),
and `H₂³` freely. -/
structure Budget {O : Type*} (p : Params) (q3 q5 qE : ℕ) (D : O → Tab3 → Sh p → Prop) : Prop where
  h3 : ∀ o s, Rd3 (fun G3 => D o G3 s) q3
  h5 : ∀ o G3, Rd5 (D o G3) q5
  hE : ∀ o G3, RdE (D o G3) qE

lemma Budget.mono {O : Type*} {p : Params} {q3 q5 qE q3' q5' qE' : ℕ} {D : O → Tab3 → Sh p → Prop}
    (h : Budget p q3 q5 qE D) (h3 : q3 ≤ q3') (h5 : q5 ≤ q5') (hE : qE ≤ qE') :
    Budget p q3' q5' qE' D :=
  ⟨fun o s => (h.h3 o s).mono h3, fun o G3 => (h.h5 o G3).mono h5, fun o G3 => (h.hE o G3).mono hE⟩

/-- An output map keeps budgets. -/
lemma Budget.comp {O O' : Type*} {p : Params} {q3 q5 qE : ℕ} (φ : O → O') {D : O' → Tab3 → Sh p → Prop}
    (h : Budget p q3 q5 qE D) : Budget p q3 q5 qE (fun o g s => D (φ o) g s) :=
  ⟨fun o s => h.h3 (φ o) s, fun o g => h.h5 (φ o) g, fun o g => h.hE (φ o) g⟩

/-- A simulated proof that is produced has the parameters' size. -/
lemma simulate_ok_size {p : Params} {c : SimCoins p} {b : ByteArray} (h : simulate p c = .ok b) :
    b.size = p.proofBytes := by
  unfold simulate at h
  split at h
  · cases h
  · injection h with h
    rw [← h]
    exact (fields_assemble p _).2.2.2.2.2.2.2.2.2

/-- **A simulation that produced no proof programs independently of the statement.** -/
lemma progRO_of_error (Hb : Hashes) {p : Params} {c : SimCoins p} {e : String}
    (h : simulate p c = .error e) (st st' : Statement) : progRO p Hb st c = progRO p Hb st' c := by
  funext s
  simp only [progRO, outPre, h]

variable (Hb : Hashes) (st : Statement) (w : ByteArray)

/-- **Zero knowledge in the ROM and ideal-cipher model, with the tables visible**
(`zk_rom_ic_h23_num` for a distinguisher with a `Budget`): the real prover (`realRO`) and the
simulator with its programming (`progRO`) are `εRO q₃ q₅ q_E`-close. -/
theorem zk_ro {cs : ByteArray → ByteArray → System GF128} (hlr : st.params.labelRows = true)
    (hzk : ZKHyp CrtGen.tables st w cs) (hHb : HashesWF Hb) (hp : SmallParams st.params)
    {q3 q5 qE : ℕ} (D : Except String ByteArray → Tab3 → Sh st.params → Prop)
    (hD : Budget st.params q3 q5 qE D) :
    |pr ((Bytes 16 × Tab3) × Sh st.params) (fun a =>
        D (realRO st.params Hb st w a.1.1 a.1.2 a.2) a.1.2 a.2) -
      pr ((SimCoins st.params × Tab3) × Sh st.params) (fun a =>
        D (simulate st.params a.1.1) a.1.2 (progRO st.params Hb st a.1.1 a.2))| ≤
      εRO q3 q5 qE := by
  choose Q3 hQ3c hQ3 using hD.h3
  choose Q5 hQ5c hQ5 using hD.h5
  choose QE hQEc hQE using hD.hE
  have key := zk_rom_ic_h23_num Hb st w hlr hzk hHb hp (fun o G3 G2 G5 E => D o G3 (G2, G5, E))
    (fun o G3 G2 G5 E => Q3 o (G2, G5, E) G3)
    (fun o G3 G3' G2 G5 E hk => Iff.of_eq (hQ3 o (G2, G5, E) G3 G3' hk).symm)
    (fun o G3 G2 G5 E => hQ3c o (G2, G5, E) G3)
    (fun o G3 G2 G5 E => Q5 o G3 (G2, G5, E))
    (fun o G3 G2 G5 G5' E hk => Iff.of_eq (hQ5 o G3 (G2, G5, E) G5' hk).symm)
    (fun o G3 G2 G5 E => hQ5c o G3 (G2, G5, E))
    (fun o G3 G2 G5 E => QE o G3 (G2, G5, E))
    (fun o G3 G2 G5 E E' hk => Iff.of_eq (hQE o G3 (G2, G5, E) E' hk).symm)
    (fun o G3 G2 G5 E => hQEc o G3 (G2, G5, E))
  let e1 : ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × Cipher ≃
      (Bytes 16 × Tab3) × Sh st.params :=
    { toFun := fun c => ((c.1.1.1, c.1.2.1), (c.1.1.2, c.1.2.2, c.2))
      invFun := fun c => (((c.1.1, c.2.1), (c.1.2, c.2.2.1)), c.2.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e2 : (SimCoins st.params × Vis2 st.params) × Cipher ≃
      (SimCoins st.params × Tab3) × Sh st.params :=
    { toFun := fun c => ((c.1.1, c.1.2.1), (c.1.2.2.1, c.1.2.2.2, c.2))
      invFun := fun c => ((c.1.1, (c.1.2, c.2.1, c.2.2.1)), c.2.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e1, ← pr_equiv e2]
  exact key

/-- **The Lean prover is `ZeroKnowledgeRO`** for every relation whose statements have dedicated
label rows (and parameters `p`) and whose witnesses satisfy the deterministic hypotheses, against
the distinguishers with budgets `(q₃, q₅, q_E)`, with error `εRO q₃ q₅ q_E`. -/
theorem lean_zeroKnowledgeRO {I W : Type*} (p : Params) (stOf : I → Statement)
    (hp : ∀ x, (stOf x).params = p) (hlr : p.labelRows = true) (enc : I → W → ByteArray)
    (R : I → W → Prop) (cs : I → ByteArray → ByteArray → System GF128)
    (h : ∀ x w, R x w → ZKHyp CrtGen.tables (stOf x) (enc x w) (cs x)) (hHb : HashesWF Hb)
    (hsp : SmallParams p) (q3 q5 qE : ℕ) :
    ZeroKnowledgeRO R (fun x w ρ G3 s => realRO p Hb (stOf x) (enc x w) ρ G3 s)
      (fun _ c => simulate p c) (fun x c s => progRO p Hb (stOf x) c s) (Budget p q3 q5 qE)
      (εRO q3 q5 qE) := by
  intro x w hxw D hD
  beta_reduce
  have hz := h x w hxw
  have hpx := hp x
  generalize stOf x = st at hz hpx ⊢
  subst hpx
  exact zk_ro Hb st (enc x w) hlr hz hHb hsp D hD

end ZKRO

end VoleMole.ZK.Sim
