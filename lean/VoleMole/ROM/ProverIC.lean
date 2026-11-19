import VoleMole.ROM.VerifyIC
import VoleMole.ZK.BavcLemmas
import VoleMole.ZK.HopsH4
import VoleMole.ZK.TapeOf

/-!
# The executable prover as an oracle computation over the hashes and the cipher

`ROM/VerifyIC.lean` runs the verifier with its hashes and its cipher evaluations as queries. Here
the same for the prover (`Prover.voleGen`, `Prover.proveCommit`, `Verifier/Prover.lean`), so that
an honest client inside a random-oracle game (PomFRIT's, `Assumptions/PomClientLean.lean`) reaches
the hashes and the ideal cipher only through the oracle `specIC`.

**The cipher.** Step 1 calls the CTR PRG (`HasPrg`) at `2304·2 + 2303 + 1` points: the children
of the `2303` internal nodes of the GGM tree, the commitment and the VOLE expansion of each of
the `2304` leaves, and `u_hi` at the root (`callsOf`). The oracle computation `cipherQ` derives
the tree with cipher queries (`treeNodeQ`, one node at a time, ancestors re-queried), then makes
each of these PRG calls with cipher queries (`prgQ`) and records the outputs. The prover then
runs with the PRG that looks the calls up (`memoPrg`). Per cipher table it is the prover with the
ideal-cipher PRG:
* `voleGenAt_congrA`: `voleGenAt` depends on the PRG only through the calls `callsOf` (computed
  from the first PRG's tree), for any two PRGs (`ZK/ReadsPoint.lean`'s `voleGenAt_ic_congrP` is
  the same for two cipher tables, at the coarser granularity of all CTR blocks of `iv`);
* `memoF_map`: the memo PRG answers each recorded call with its recorded output.

**The hashes** are queried as the verifier does (`hashQ`, `mu1Q`, `muDelayedQ`, `combBytesQ`).

**Results.**
* `step1Q`, **`eval_step1Q`**: against complete tables `g` (hashes) and `E` (cipher), step 1 is
  `Prover.voleGen` with the hashes of `g` and the ideal-cipher PRG `icPrg E.cipher`.
* `proveCommitQ`, **`eval_proveCommitQ`**: step 2 (hash queries only; the grinding loop is
  `findFirstQ`) is `Prover.proveCommit` with the hashes of `g`.
* `preGQ`, `eval_preGQ`: step 2's grinding prefix `chal2 ‖ qs_check ‖ ã` (`ZK.Sim.realPre`), with
  no `H₂³` query (`allQ_preGQ`); `blockQ`, `eval_blockQ`: the `2³²` `H₂³` answers at a prefix's
  grinding points (`ZK.Sim.realGrind`).
* `allQ_step1Q`: step 1 makes no `H₂³` query.

No `sorry`, no `axiom`.
-/

open OracleComp OracleSpec

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim VoleMole.ROM

/-! ## Two PRGs that agree on the prover's calls -/

section Congr

/-- **Two PRGs agree on one call** `prg key iv t c n`. -/
def PrgAgree (P P' : HasPrg) (key iv : ByteArray) (t c : UInt32) (n : ℕ) : Prop :=
  @HasPrg.prg P key iv t c n = @HasPrg.prg P' key iv t c n

/-- The leaves `(i, j)`, `i < τ`, `j < 2^{k_i}`. -/
def leafIdx : List (ℕ × ℕ) :=
  (List.range BAVC.tau).flatMap fun i => (List.range (2 ^ BAVC.kOf i)).map fun j => (i, j)

lemma mem_leafIdx {i j : ℕ} (hi : i < BAVC.tau) (hj : j < 2 ^ BAVC.kOf i) : (i, j) ∈ leafIdx := by
  simp only [leafIdx, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  exact ⟨i, hi, j, hj, rfl, rfl⟩

lemma of_mem_leafIdx {x : ℕ × ℕ} (h : x ∈ leafIdx) : x.1 < BAVC.tau ∧ x.2 < 2 ^ BAVC.kOf x.1 := by
  simp only [leafIdx, List.mem_flatMap, List.mem_range, List.mem_map] at h
  obtain ⟨i, hi, j, hj, rfl⟩ := h
  exact ⟨hi, hj⟩

/-- **The prover's PRG calls agree**: the tree's children, the leaves' commitments and VOLE
expansions, and `u_hi`, at the nodes of the tree computed with `P`. -/
structure CallsAgree (P P' : HasPrg) (p : Params) (seed iv : ByteArray) : Prop where
  tree : ∀ m < BAVC.numLeaves - 1, PrgAgree P P' (@treeNode P seed iv m) iv m.toUInt32 0 2
  com : ∀ i < BAVC.tau, ∀ j < 2 ^ BAVC.kOf i,
    PrgAgree P P' (@treeNode P seed iv (BAVC.treePos i j)) iv (i + BAVC.numLeaves - 1).toUInt32 0 2
  vole : ∀ i < BAVC.tau, ∀ j < 2 ^ BAVC.kOf i,
    PrgAgree P P' (@treeNode P seed iv (BAVC.treePos i j)) iv (((1 : UInt32) <<< 31) + i.toUInt32) 0
      p.voleColBlocks
  hi : PrgAgree P P' seed iv (((1 : UInt32) <<< 31) - 1) 0 ((8 * p.nMask + 127) / 128)

variable {P P' : HasPrg} {p : Params} {seed iv : ByteArray}

theorem treeNode_congrA
    (h : ∀ m < BAVC.numLeaves - 1, PrgAgree P P' (@treeNode P seed iv m) iv m.toUInt32 0 2) :
    ∀ n < BAVC.numNodes, @treeNode P seed iv n = @treeNode P' seed iv n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases n with _ | m
    · rw [@treeNode.eq_1 P, @treeNode.eq_1 P']
    · rw [@treeNode.eq_2 P, @treeNode.eq_2 P', ← ih (m / 2) (by omega) (by omega)]
      unfold BAVC.children
      rw [h (m / 2) (by simp only [BAVC.numNodes, BAVC.numLeaves] at hn ⊢; omega)]

theorem expandTree_congrA (hs : seed.size = 16)
    (h : ∀ m < BAVC.numLeaves - 1, PrgAgree P P' (@treeNode P seed iv m) iv m.toUInt32 0 2) :
    @BAVC.expandTree P seed iv = @BAVC.expandTree P' seed iv := by
  have s1 := (@expandTree_spec P seed iv hs).1
  have s2 := (@expandTree_spec P' seed iv hs).1
  refine Array.ext (by rw [s1, s2]) fun i h1 h2 => ?_
  have hi : i < BAVC.numNodes := by rwa [s1] at h1
  rw [← getElem!_pos _ i h1, ← getElem!_pos _ i h2, @expandTree_get P _ _ _ hi,
    @expandTree_get P' _ _ _ hi]
  exact treeNode_congrA h i hi

theorem commit_congrA (hs : seed.size = 16) (h : CallsAgree P P' p seed iv) :
    @BAVC.commit P seed iv = @BAVC.commit P' seed iv := by
  unfold BAVC.commit
  dsimp only
  rw [expandTree_congrA hs h.tree, @leavesOf_eq P, @leavesOf_eq P']
  simp only [Prod.mk.injEq, BAVC.Leaves.mk.injEq, true_and]
  apply congrArg (List.foldl (· ++ ·) ByteArray.empty)
  refine pieces_congr fun i hi j hj => ?_
  split_ifs
  · rfl
  · have hn := treePos_lt hi hj
    rw [@expandTree_get P' _ _ _ hn, ← treeNode_congrA h.tree _ hn]
    exact h.com i hi j hj

theorem smallVoleUWords_congrA (i : ℕ) (key : ℕ → ByteArray)
    (h : ∀ j < 2 ^ BAVC.kOf i,
      PrgAgree P P' (key j) iv (((1 : UInt32) <<< 31) + i.toUInt32) 0 p.voleColBlocks) :
    @Prover.smallVoleUWords P p iv i key = @Prover.smallVoleUWords P' p iv i key := by
  unfold Prover.smallVoleUWords
  refine List.foldl_ext _ _ _ fun acc j hj => ?_
  simp only [prgWords]
  rw [h j (List.mem_range.1 hj)]

theorem convertToVoleAt_congrA (dbit : ℕ → Bool) (corr : ℕ → ByteArray) (key : ℕ → ℕ → ByteArray)
    (h : ∀ i < BAVC.tau, ∀ j < 2 ^ BAVC.kOf i,
      PrgAgree P P' (key i j) iv (((1 : UInt32) <<< 31) + i.toUInt32) 0 p.voleColBlocks) :
    @convertToVoleAt P p dbit corr iv key = @convertToVoleAt P' p dbit corr iv key := by
  have ht : ∀ i < BAVC.tau, @treeColumns P p iv i (BAVC.hiddenIndex dbit i) (corr i) (key i) =
      @treeColumns P' p iv i (BAVC.hiddenIndex dbit i) (corr i) (key i) := by
    intro i hi
    have hp : @prgOuts P p iv i (BAVC.hiddenIndex dbit i) (key i) =
        @prgOuts P' p iv i (BAVC.hiddenIndex dbit i) (key i) := by
      unfold prgOuts
      refine Array.map_congr_left fun j hj => ?_
      have hj := Array.mem_range.1 hj
      split_ifs
      · rfl
      · simp only [prgWords]
        rw [h i hi j hj]
    simp only [treeColumns, hp]
  have htr : ((Array.range BAVC.tau).map fun i =>
      @treeColumns P p iv i (BAVC.hiddenIndex dbit i) (corr i) (key i)) =
      (Array.range BAVC.tau).map fun i =>
        @treeColumns P' p iv i (BAVC.hiddenIndex dbit i) (corr i) (key i) :=
    Array.map_congr_left fun i hi => ht i (Array.mem_range.1 hi)
  simp only [convertToVoleAt, htr]

/-- **Step 1 depends on the PRG only through its calls** (`CallsAgree`). -/
theorem voleGenAt_congrA (Hs : Hashes) (T : CrtTables) (mu1 wPrefix ivPre binder1 : ByteArray)
    (hs : seed.size = 16) (h : CallsAgree P P' p seed (Hs.hash .h4 ((ivPre ++ mu1).push 4))) :
    @voleGenAt P Hs T p mu1 wPrefix seed ivPre binder1 =
      @voleGenAt P' Hs T p mu1 wPrefix seed ivPre binder1 := by
  set iv := Hs.hash .h4 ((ivPre ++ mu1).push 4) with hiv
  have hc := commit_congrA hs h
  have hk : ∀ i j, i < BAVC.tau → j < 2 ^ BAVC.kOf i →
      leafKey (@BAVC.commit P' seed iv).2 i j = @treeNode P seed iv (BAVC.treePos i j) :=
    fun i j hi hj => by
      rw [@leafKey_commit P' seed iv hs i j hi hj, treeNode_congrA h.tree _ (treePos_lt hi hj)]
  have hus : (Array.range BAVC.tau).map (fun i =>
      @Prover.smallVoleUWords P p iv i (leafKey (@BAVC.commit P' seed iv).2 i)) =
      (Array.range BAVC.tau).map (fun i =>
        @Prover.smallVoleUWords P' p iv i (leafKey (@BAVC.commit P' seed iv).2 i)) :=
    Array.map_congr_left fun i hi => smallVoleUWords_congrA _ _ fun j hj => by
      have hi' := Array.mem_range.1 hi
      rw [hk i j hi' hj]
      exact h.vole i hi' j hj
  have hcols : @Prover.senderColumns P p iv (leafKey (@BAVC.commit P' seed iv).2) =
      @Prover.senderColumns P' p iv (leafKey (@BAVC.commit P' seed iv).2) := by
    unfold Prover.senderColumns
    refine convertToVoleAt_congrA _ _ _ fun i hi j hj => ?_
    rw [hk i j hi hj]
    exact h.vole i hi j hj
  have hum : ∀ us, @Prover.uMaskOf P p T seed iv us = @Prover.uMaskOf P' p T seed iv us :=
    fun us => by
      unfold Prover.uMaskOf
      rw [h.hi]
  simp only [voleGenAt, ← hiv, hc, hus, hcols, hum]

end Congr

/-! ## The PRG of recorded calls -/

section Memo

/-- A PRG call `(key, iv, tweak, counter, blocks)`. -/
abbrev Call := ByteArray × ByteArray × UInt32 × UInt32 × ℕ

/-- **The recorded output of a call** (fitted to `16 n` bytes; zero if not recorded). -/
def memoF (M : List (Call × ByteArray)) (key iv : ByteArray) (t c : UInt32) (n : ℕ) : ByteArray :=
  Prover.fit (((M.find? fun e => decide (e.1 = (key, iv, t, c, n))).map Prod.snd).getD .empty)
    (16 * n)

/-- **The PRG of recorded calls.** -/
@[reducible] def memoPrg (M : List (Call × ByteArray)) : HasPrg := ⟨memoF M, fun _ _ _ _ n => fit_size _ (16 * n)⟩

lemma find?_map_self (calls : List Call) (f : Call → ByteArray) {x : Call} (hx : x ∈ calls) :
    ((calls.map fun y => (y, f y)).find? fun e => decide (e.1 = x)) = some (x, f x) := by
  induction calls with
  | nil => simp at hx
  | cons y l ih =>
    rw [List.map_cons, List.find?_cons]
    by_cases hy : y = x
    · subst hy; simp
    · have hx' : x ∈ l := (List.mem_cons.1 hx).resolve_left (Ne.symm hy)
      simp only [hy, decide_false]
      exact ih hx'

/-- **The memo PRG answers each recorded call with its recorded output.** -/
lemma memoF_map (calls : List Call) (f : Call → ByteArray)
    (hf : ∀ x ∈ calls, (f x).size = 16 * x.2.2.2.2) {x : Call} (hx : x ∈ calls) :
    memoF (calls.map fun y => (y, f y)) x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 = f x := by
  unfold memoF
  rw [show ((x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2) : Call) = x from rfl,
    find?_map_self calls f hx]
  exact fit_of_size (hf x hx)

/-- **The prover's PRG calls**, from its tree's nodes `node`: the children of the internal nodes,
then the leaves' commitments, then their VOLE expansions, then `u_hi`. -/
def callsOf (p : Params) (seed iv : ByteArray) (node : ℕ → ByteArray) : List Call :=
  (List.range (BAVC.numLeaves - 1)).map (fun m => ((node m, iv, m.toUInt32, 0, 2) : Call)) ++
    leafIdx.map (fun ij => ((node (BAVC.treePos ij.1 ij.2), iv,
      (ij.1 + BAVC.numLeaves - 1).toUInt32, 0, 2) : Call)) ++
    leafIdx.map (fun ij => ((node (BAVC.treePos ij.1 ij.2), iv,
      ((1 : UInt32) <<< 31) + ij.1.toUInt32, 0, p.voleColBlocks) : Call)) ++
    [((seed, iv, ((1 : UInt32) <<< 31) - 1, 0, (8 * p.nMask + 127) / 128) : Call)]

/-- The outputs of a PRG on a list of calls. -/
def outsOf (P : HasPrg) (calls : List Call) : List (Call × ByteArray) :=
  calls.map fun x => (x, @HasPrg.prg P x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)

/-- **A PRG agrees with the memo PRG of its own outputs on the prover's calls.** -/
theorem callsAgree_memo (P : HasPrg) (p : Params) (seed iv : ByteArray) :
    CallsAgree P (memoPrg (outsOf P (callsOf p seed iv (@treeNode P seed iv)))) p seed iv := by
  have key : ∀ x ∈ callsOf p seed iv (@treeNode P seed iv),
      PrgAgree P (memoPrg (outsOf P (callsOf p seed iv (@treeNode P seed iv))))
        x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 := fun x hx =>
    (memoF_map _ (fun x => @HasPrg.prg P x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)
      (fun x _ => @HasPrg.prg_size P _ _ _ _ _) hx).symm
  refine ⟨fun m hm => key (@treeNode P seed iv m, iv, m.toUInt32, 0, 2) ?_,
    fun i hi j hj => key (@treeNode P seed iv (BAVC.treePos i j), iv,
      (i + BAVC.numLeaves - 1).toUInt32, 0, 2) ?_,
    fun i hi j hj => key (@treeNode P seed iv (BAVC.treePos i j), iv,
      ((1 : UInt32) <<< 31) + i.toUInt32, 0, p.voleColBlocks) ?_,
    key (seed, iv, ((1 : UInt32) <<< 31) - 1, 0, (8 * p.nMask + 127) / 128) ?_⟩
  · simp only [callsOf, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inl (Or.inl (Or.inl ⟨m, hm, rfl⟩))
  · simp only [callsOf, List.mem_append, List.mem_map]
    exact Or.inl (Or.inl (Or.inr ⟨(i, j), mem_leafIdx hi hj, rfl⟩))
  · simp only [callsOf, List.mem_append, List.mem_map]
    exact Or.inl (Or.inr ⟨(i, j), mem_leafIdx hi hj, rfl⟩)
  · simp [callsOf]

end Memo

/-! ## Step 1 as an oracle computation -/

section Step1

/-- **A node of the GGM tree with cipher queries** (its ancestors re-derived). -/
def treeNodeQ (seed iv : ByteArray) : ℕ → OracleComp specIC ByteArray
  | 0 => pure seed
  | n + 1 => do
    let par ← treeNodeQ seed iv (n / 2)
    let c ← prgQ par iv (n / 2).toUInt32 0 2
    pure (BAVC.block c (n % 2))
decreasing_by omega

/-- One PRG call with cipher queries, recorded. -/
def callQ (x : Call) : OracleComp specIC (Call × ByteArray) :=
  (fun b => (x, b)) <$> prgQ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2

/-- **The prover's cipher queries**: the tree's nodes, then each of the prover's PRG calls. -/
@[irreducible] def cipherQ (p : Params) (seed iv : ByteArray) : OracleComp specIC (List (Call × ByteArray)) := do
  let nodes ← (List.range BAVC.numNodes).mapM (treeNodeQ seed iv)
  (callsOf p seed iv (fun m => nodes.getD m .empty)).mapM callQ

variable (g : Table) (E : CTable)

theorem eval_treeNodeQ (seed iv : ByteArray) :
    ∀ n, evalWithAnswerFn (QueryImpl.ofFn (join g E)) (treeNodeQ seed iv n) =
      @treeNode (icPrg E.cipher) seed iv n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | m
    · rw [treeNodeQ, @treeNode.eq_1 (icPrg E.cipher)]; rfl
    · rw [treeNodeQ, @treeNode.eq_2 (icPrg E.cipher)]
      simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, evalWithAnswerFn_prgQ,
        ih (m / 2) (by omega)]
      rfl

lemma callsOf_congr (p : Params) (seed iv : ByteArray) {f f' : ℕ → ByteArray}
    (h : ∀ m < BAVC.numNodes, f m = f' m) : callsOf p seed iv f = callsOf p seed iv f' := by
  have hl : ∀ ij ∈ leafIdx, f (BAVC.treePos ij.1 ij.2) = f' (BAVC.treePos ij.1 ij.2) :=
    fun ij hij => h _ (treePos_lt (of_mem_leafIdx hij).1 (of_mem_leafIdx hij).2)
  have e1 : (List.range (BAVC.numLeaves - 1)).map (fun m => ((f m, iv, m.toUInt32, 0, 2) : Call)) =
      (List.range (BAVC.numLeaves - 1)).map (fun m => ((f' m, iv, m.toUInt32, 0, 2) : Call)) :=
    List.map_congr_left fun m hm => by
      rw [h m (by simp only [List.mem_range, BAVC.numNodes, BAVC.numLeaves] at hm ⊢; omega)]
  have e2 : leafIdx.map (fun ij => ((f (BAVC.treePos ij.1 ij.2), iv,
      (ij.1 + BAVC.numLeaves - 1).toUInt32, 0, 2) : Call)) =
      leafIdx.map (fun ij => ((f' (BAVC.treePos ij.1 ij.2), iv,
        (ij.1 + BAVC.numLeaves - 1).toUInt32, 0, 2) : Call)) :=
    List.map_congr_left fun ij hij => by rw [hl ij hij]
  have e3 : leafIdx.map (fun ij => ((f (BAVC.treePos ij.1 ij.2), iv,
      ((1 : UInt32) <<< 31) + ij.1.toUInt32, 0, p.voleColBlocks) : Call)) =
      leafIdx.map (fun ij => ((f' (BAVC.treePos ij.1 ij.2), iv,
        ((1 : UInt32) <<< 31) + ij.1.toUInt32, 0, p.voleColBlocks) : Call)) :=
    List.map_congr_left fun ij hij => by rw [hl ij hij]
  unfold callsOf
  rw [e1, e2, e3]

/-- **Per cipher table, `cipherQ` records the ideal-cipher PRG's outputs on the prover's calls.** -/
theorem eval_cipherQ (p : Params) (seed iv : ByteArray) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) (cipherQ p seed iv) =
      outsOf (icPrg E.cipher) (callsOf p seed iv (@treeNode (icPrg E.cipher) seed iv)) := by
  unfold cipherQ
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_mapM, eval_treeNodeQ]
  rw [callsOf_congr p seed iv (f' := @treeNode (icPrg E.cipher) seed iv) fun m hm => by
    rw [List.getD_eq_getElem _ _ (by simpa using hm)]
    simp]
  unfold outsOf callQ
  refine List.map_congr_left fun x _ => ?_
  rw [evalWithAnswerFn_map, evalWithAnswerFn_prgQ]

/-- **Step 1 after `iv`, with the hashes as queries** and the PRG `P` (`voleGenAt`'s body). -/
def vgTailQ (P : HasPrg) (T : CrtTables) (p : Params) (mu1 wPrefix seed ivPre iv binder1 : ByteArray) :
    OracleComp spec Prover.Pending := do
  let tl := @BAVC.commit P seed iv
  let tree := tl.1
  let leaves := tl.2
  let lh ← (BAVC.leafHashInputs leaves.coms).mapM (hashQ .h1)
  let check ← hashQ .h1 (BAVC.comInput lh)
  let key := leafKey leaves
  let us : Array (Array UInt64) :=
    (Array.range BAVC.tau).map fun i => @Prover.smallVoleUWords P p iv i (key i)
  let u := us[0]!
  let cols := @Prover.senderColumns P p iv key
  let corrections := (List.range (BAVC.tau - 1)).foldl
    (fun acc i => acc ++ Prover.correctionOf p u us[i + 1]!) ByteArray.empty
  let uPre : W128 := ⟨wordAt u p.labelRowOffset, wordAt u (p.labelRowOffset + 64)⟩
  let hs0 ← (Prover.gateInputsOff p T iv cols W128.zero).mapM (hashQ .h5)
  let hs1 ← (Prover.gateInputsOff p T iv cols uPre).mapM (hashQ .h5)
  let h0 := gateWords hs0
  let h1 := gateWords hs1
  let vOut := crtReconstructWith h0 p (fun _ => false) ByteArray.empty T cols
  let uMask := @Prover.uMaskOf P p T seed iv us
  let cmult := Prover.cMultOf p h0 h1 uMask
  let f0 : Prover.Fields :=
    { corrections := corrections, cmult := cmult, voleCheck := .empty, correction := .empty,
      qsProof := .empty, opening := .empty, delta := .empty, ivPre := ivPre, ctr := .empty }
  let c1 ← hashQ .h21 (chal1Input { params := p, bytes := Prover.assemble p f0 } mu1 check binder1)
  let uRows : Array W128 := (Array.range p.correctionRows).map fun r =>
    if wbit u r then ⟨1, 0⟩ else W128.zero
  let uTilde := voleHashReceiver p c1 uRows uMask 0 (Prover.zeros 64)
  let hV := voleHashReceiver p c1 vOut.rows vOut.qMask 0 (Prover.zeros 64)
  let voleCheck := Prover.gfsToBytes uTilde
  let ub := bytesOfWords u
  let correction : ByteArray :=
    ⟨(Array.range wPrefix.size).map fun k => ub.get! k ^^^ wPrefix.get! k⟩
  let fs : Prover.Fields := { f0 with voleCheck := voleCheck, correction := correction }
  pure (Prover.Pending.mk p seed iv ivPre tree leaves u vOut.rows vOut.qMask uMask c1 hV wPrefix fs)

theorem eval_vgTailQ (P : HasPrg) (T : CrtTables) (p : Params)
    (mu1 wPrefix seed ivPre binder1 : ByteArray) :
    evalWithAnswerFn (QueryImpl.ofFn g) (vgTailQ P T p mu1 wPrefix seed ivPre
        ((Hashes.ofTable g).hash .h4 ((ivPre ++ mu1).push 4)) binder1) =
      @voleGenAt P (Hashes.ofTable g) T p mu1 wPrefix seed ivPre binder1 := by
  simp only [vgTailQ, evalWithAnswerFn_bind, evalWithAnswerFn_mapM_hashQ, evalWithAnswerFn_hashQ,
    evalWithAnswerFn_pure]
  rfl

/-- **Step 1 as an oracle computation** (`Prover.voleGen`): `H₃`, `H₄`, the cipher queries of the
prover's PRG calls, then the rest with the PRG of the recorded calls and the hashes as queries. -/
def step1Q (T : CrtTables) (p : Params) (mu1 wPrefix rho binder1 : ByteArray) :
    OracleComp specIC Prover.Pending := do
  let h3 ← liftIC (hashQ .h3 ((wPrefix ++ mu1 ++ rho).push 3))
  let seed := h3.extract 0 16
  let ivPre := h3.extract 16 32
  let iv ← liftIC (hashQ .h4 ((ivPre ++ mu1).push 4))
  let M ← cipherQ p seed iv
  liftIC (vgTailQ (memoPrg M) T p mu1 wPrefix seed ivPre iv binder1)

/-- **Per table, step 1 is the executable `voleGen`** with the hashes of `g` and the ideal-cipher
PRG of `E`. -/
theorem eval_step1Q (T : CrtTables) (p : Params) (mu1 wPrefix rho binder1 : ByteArray) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) (step1Q T p mu1 wPrefix rho binder1) =
      @Prover.voleGen (icPrg E.cipher) (Hashes.ofTable g) T p mu1 wPrefix rho binder1 := by
  set Hs := Hashes.ofTable g
  set h3 := Hs.hash .h3 ((wPrefix ++ mu1 ++ rho).push 3) with hh3
  have hs : (h3.extract 0 16).size = 16 := by
    rw [ByteArray.size_extract, hh3, Hashes.ofTable_hash, Bytes.size_ba]; rfl
  simp only [step1Q, evalWithAnswerFn_bind, evalWithAnswerFn_liftIC, evalWithAnswerFn_hashQ,
    eval_cipherQ]
  rw [eval_vgTailQ, @voleGen_eq_voleGenAt (icPrg E.cipher)]
  exact (voleGenAt_congrA Hs T mu1 wPrefix _ binder1 hs (callsAgree_memo _ _ _ _)).symm

end Step1

/-! ## Step 2 as an oracle computation -/

section Step2

/-- `findFirst` with the attempts as oracle computations. -/
def findFirstQ {α : Type} (f : ℕ → OracleComp spec (Option α)) : ℕ → ℕ → OracleComp spec (Option α)
  | 0, _ => pure none
  | fuel + 1, c => f c >>= fun r => match r with
    | some a => pure (some a)
    | none => findFirstQ f fuel (c + 1)

/-- One grinding attempt with its `H₂³` query (`Prover.grindStep`). -/
def grindStepQ (s : Prover.Pending) (pre : ByteArray) (ctr : ℕ) :
    OracleComp spec (Option (ℕ × ByteArray × ByteArray)) :=
  (fun delta => if delta.get! 15 == 0 then
      (BAVC.openAt s.tree s.leaves.coms delta).map fun o => (ctr, delta, o)
    else none) <$> hashQ .h23 ((AES.pushLE32 pre ctr.toUInt32).push 11)

/-- Step 2's fields before `chal2` (`d` on the whole witness). -/
def pcF1 (s : Prover.Pending) (w : ByteArray) : Prover.Fields :=
  { s.fields with correction :=
    ⟨(Array.range s.params.witnessBytes).map fun k => (bytesOfWords s.u).get! k ^^^ w.get! k⟩ }

/-- The final proof from step 2's fields, `ã`, the opening, `Δ` and the counter. -/
def pcOut (s : Prover.Pending) (w qsProof opening delta : ByteArray) (ctr : ℕ) : ByteArray :=
  Prover.assemble s.params
    { pcF1 s w with
      qsProof := qsProof, opening := opening, delta := delta,
      ctr := AES.pushLE32 ByteArray.empty ctr.toUInt32 }

/-- **Step 2 as an oracle computation** (`Prover.proveCommit`): `chal2`, PomFRIT's `mu` and the
combination as queries, QuickSilver, then the grinding loop with one `H₂³` query per attempt. -/
def proveCommitQ (st : Statement) (wSuffix : ByteArray) (s : Prover.Pending) :
    OracleComp spec (Except String ByteArray) :=
  if (s.wPrefix ++ wSuffix).size != s.params.witnessBytes then
    pure (.error "witness: wrong length")
  else do
    let w := s.wPrefix ++ wSuffix
    let pf1 : Proof := { params := s.params, bytes := Prover.assemble s.params (pcF1 s w) }
    let muD ← muDelayedQ st s.chal1
    let c2 ← hashQ .h22 (chal2Input pf1 s.chal1 s.hV muD st.binder2)
    let lb ← combBytesQ st c2
    match Prover.qsProve pf1 c2 (st.values s.chal1 lb) s.vRows s.vMask s.uMask w with
    | .error e => pure (.error e)
    | .ok (check, aT) =>
      findFirstQ (grindStepQ s (c2 ++ gfToBytes check ++ Prover.gfsToBytes aT)) (2 ^ 32) 0 >>=
        fun r => match r with
        | none => pure (.error "grinding failed")
        | some (ctr, delta, opening) => pure (.ok (pcOut s w (Prover.gfsToBytes aT) opening delta ctr))

variable (g : Table)

theorem eval_findFirstQ {α : Type} (f : ℕ → OracleComp spec (Option α)) :
    ∀ fuel c, evalWithAnswerFn (QueryImpl.ofFn g) (findFirstQ f fuel c) =
      Prover.findFirst (fun c => evalWithAnswerFn (QueryImpl.ofFn g) (f c)) fuel c
  | 0, _ => rfl
  | fuel + 1, c => by
    simp only [findFirstQ, Prover.findFirst, evalWithAnswerFn_bind]
    cases evalWithAnswerFn (QueryImpl.ofFn g) (f c) with
    | some a => rfl
    | none => exact eval_findFirstQ f fuel (c + 1)

lemma eval_grindStepQ (s : Prover.Pending) (pre : ByteArray) (ctr : ℕ) :
    evalWithAnswerFn (QueryImpl.ofFn g) (grindStepQ s pre ctr) =
      Prover.grindStep (Hashes.ofTable g) s pre ctr := by
  simp only [grindStepQ, evalWithAnswerFn_map, evalWithAnswerFn_hashQ, Prover.grindStep]
  rfl

/-- **Per table, step 2 is the executable `proveCommit`** with the hashes of `g`. -/
theorem eval_proveCommitQ (st : Statement) (wSuffix : ByteArray) (s : Prover.Pending) :
    evalWithAnswerFn (QueryImpl.ofFn g) (proveCommitQ st wSuffix s) =
      Prover.proveCommit (Hashes.ofTable g) st wSuffix s := by
  unfold proveCommitQ Prover.proveCommit
  by_cases hw : ((s.wPrefix ++ wSuffix).size != s.params.witnessBytes) = true
  · simp only [hw, ite_true]
    rfl
  · simp only [hw, Bool.false_eq_true, ite_false, evalWithAnswerFn_bind, evalWithAnswerFn_muDelayedQ,
      evalWithAnswerFn_hashQ, evalWithAnswerFn_combBytesQ]
    simp only [pcF1, chal2]
    split
    · rename_i e heq
      simp only [heq]
      rfl
    · rename_i check aT heq
      simp only [heq, evalWithAnswerFn_bind, eval_findFirstQ, eval_grindStepQ]
      split
      · rename_i hf
        simp only [bind, Except.bind, hf]
        rfl
      · rename_i ctr delta opening hf
        simp only [bind, Except.bind, hf]
        rfl

/-- **Step 2's grinding prefix with its hash queries** (`ZK.Sim.realPre`: `chal2 ‖ qs_check ‖ ã`,
empty if QuickSilver fails). -/
def preGQ (st : Statement) (s : Prover.Pending) (w : ByteArray) : OracleComp spec ByteArray := do
  let pf1 : Proof := { params := st.params, bytes := Prover.assemble st.params (realF1 st.params s w) }
  let muD ← muDelayedQ st s.chal1
  let c2 ← hashQ .h22 (chal2Input pf1 s.chal1 s.hV muD st.binder2)
  let lb ← combBytesQ st c2
  pure (match Prover.qsProve pf1 c2 (st.values s.chal1 lb) s.vRows s.vMask s.uMask w with
    | .ok (check, aT) => c2 ++ gfToBytes check ++ Prover.gfsToBytes aT
    | .error _ => ByteArray.empty)

theorem eval_preGQ (st : Statement) (s : Prover.Pending) (w : ByteArray) :
    evalWithAnswerFn (QueryImpl.ofFn g) (preGQ st s w) = realPre (Hashes.ofTable g) st s w := by
  simp only [preGQ, evalWithAnswerFn_bind, evalWithAnswerFn_muDelayedQ, evalWithAnswerFn_hashQ,
    evalWithAnswerFn_combBytesQ, evalWithAnswerFn_pure]
  rfl

/-- The grinding points of a prefix, `pre ‖ ctr ‖ 11`, `ctr < 2³²`. -/
def grindIns (pre : ByteArray) : List ByteArray :=
  (List.finRange nGrind).map fun c => (AES.pushLE32 pre c.val.toUInt32).push 11

/-- **The `H₂³` answers at a prefix's `2³²` grinding points**, all queried. -/
def blockQ (pre : ByteArray) : OracleComp spec (Fin nGrind → ZK.Sim.Bytes 16) :=
  (fun l c => VoleMole.ZK.Sim.blk 16 (l.getD c.val .empty)) <$> (grindIns pre).mapM (hashQ .h23)

theorem eval_blockQ (pre : ByteArray) :
    evalWithAnswerFn (QueryImpl.ofFn g) (blockQ pre) = realGrind (Hashes.ofTable g) pre := by
  simp only [blockQ, evalWithAnswerFn_map, evalWithAnswerFn_mapM_hashQ]
  funext c
  simp only [grindIns, List.map_map, realGrind]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

end Step2

/-! ## Which oracles the two steps query -/

section Queries

/-- Not an `H₂³` query. -/
def NoH23 (d : Dom) : Prop := d.1 ≠ .h23

/-- Not an `H₂³` query (a cipher query, or a hash query of another kind). -/
def NoH23IC : DomIC → Prop
  | .inl d => d.1 ≠ .h23
  | .inr _ => True

variable {ι : Type} {sp : OracleSpec ι} {α β : Type}

lemma allQ_map {oa : OracleComp sp α} {P : ι → Prop} (f : α → β) (h : AllQueriesSatisfy oa P) :
    AllQueriesSatisfy (f <$> oa) P := by
  rw [map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind h fun _ => allQueriesSatisfy_pure _ _

lemma allQ_mapM {P : ι → Prop} (f : α → OracleComp sp β) :
    ∀ (l : List α), (∀ a ∈ l, AllQueriesSatisfy (f a) P) → AllQueriesSatisfy (l.mapM f) P
  | [], _ => by simp
  | a :: l, h => by
    rw [List.mapM_cons]
    exact allQueriesSatisfy_bind (h a List.mem_cons_self) fun _ =>
      allQueriesSatisfy_bind (allQ_mapM f l fun b hb => h b (List.mem_cons_of_mem _ hb)) fun _ =>
        allQueriesSatisfy_pure _ _

lemma allQ_hashQ {k : Kind} (hk : k ≠ .h23) (x : ByteArray) : AllQueriesSatisfy (hashQ k x) NoH23 :=
  allQ_map _ ((allQueriesSatisfy_query_iff _ _).2 hk)

lemma allQ_mapM_hashQ {k : Kind} (hk : k ≠ .h23) (l : List ByteArray) :
    AllQueriesSatisfy (l.mapM (hashQ k)) NoH23 :=
  allQ_mapM _ l fun x _ => allQ_hashQ hk x

lemma allQ_liftIC {oa : OracleComp spec α} (h : AllQueriesSatisfy oa NoH23) :
    AllQueriesSatisfy (liftIC oa) NoH23IC := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact allQueriesSatisfy_pure _ _
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h
    rw [liftIC_query_bind, allQueriesSatisfy_query_bind_iff]
    exact ⟨h.1, fun u => ih u (h.2 u)⟩

lemma allQ_prgQ (key iv : ByteArray) (t c : UInt32) (n : ℕ) :
    AllQueriesSatisfy (prgQ key iv t c n) NoH23IC := by
  unfold prgQ
  split_ifs
  · exact allQ_map _ (allQ_mapM _ _ fun x _ => (allQueriesSatisfy_query_iff _ _).2 trivial)
  · exact allQueriesSatisfy_pure _ _

lemma allQ_treeNodeQ (seed iv : ByteArray) : ∀ n, AllQueriesSatisfy (treeNodeQ seed iv n) NoH23IC
  | 0 => by rw [treeNodeQ]; exact allQueriesSatisfy_pure _ _
  | n + 1 => by
    rw [treeNodeQ]
    exact allQueriesSatisfy_bind (allQ_treeNodeQ seed iv (n / 2)) fun _ =>
      allQueriesSatisfy_bind (allQ_prgQ _ _ _ _ _) fun _ => allQueriesSatisfy_pure _ _
decreasing_by omega

lemma allQ_cipherQ (p : Params) (seed iv : ByteArray) :
    AllQueriesSatisfy (cipherQ p seed iv) NoH23IC := by
  unfold cipherQ
  generalize List.range BAVC.numNodes = l
  refine allQueriesSatisfy_bind (allQ_mapM _ l fun n _ => allQ_treeNodeQ seed iv n) fun nodes => ?_
  generalize callsOf p seed iv _ = cs
  exact allQ_mapM _ cs fun x _ => allQ_map _ (allQ_prgQ _ _ _ _ _)

lemma allQ_vgTailQ (P : HasPrg) (T : CrtTables) (p : Params)
    (mu1 wPrefix seed ivPre iv binder1 : ByteArray) :
    AllQueriesSatisfy (vgTailQ P T p mu1 wPrefix seed ivPre iv binder1) NoH23 := by
  unfold vgTailQ
  exact allQueriesSatisfy_bind (allQ_mapM_hashQ (by decide) _) fun _ =>
    allQueriesSatisfy_bind (allQ_hashQ (by decide) _) fun _ =>
    allQueriesSatisfy_bind (allQ_mapM_hashQ (by decide) _) fun _ =>
    allQueriesSatisfy_bind (allQ_mapM_hashQ (by decide) _) fun _ =>
    allQueriesSatisfy_bind (allQ_hashQ (by decide) _) fun _ => allQueriesSatisfy_pure _ _

/-- **Step 1 makes no `H₂³` query.** -/
theorem allQ_step1Q (T : CrtTables) (p : Params) (mu1 wPrefix rho binder1 : ByteArray) :
    AllQueriesSatisfy (step1Q T p mu1 wPrefix rho binder1) NoH23IC := by
  unfold step1Q
  refine allQueriesSatisfy_bind (allQ_liftIC (allQ_hashQ (by decide) _)) fun h3 => ?_
  refine allQueriesSatisfy_bind (allQ_liftIC (allQ_hashQ (by decide) _)) fun iv => ?_
  refine allQueriesSatisfy_bind (allQ_cipherQ p (h3.extract 0 16) iv) fun M => ?_
  exact allQ_liftIC (allQ_vgTailQ _ _ _ _ _ _ _ _ _)

lemma allQ_muDelayedQ (st : Statement) (c1 : ByteArray) : AllQueriesSatisfy (muDelayedQ st c1) NoH23 := by
  unfold muDelayedQ
  split_ifs
  · exact allQ_hashQ (by decide) _
  · exact allQueriesSatisfy_pure _ _

lemma allQ_mu1Q (st : Statement) : AllQueriesSatisfy (mu1Q st) NoH23 := by
  unfold mu1Q
  split_ifs
  · exact allQ_hashQ (by decide) _
  · exact allQ_hashQ (by decide) _

lemma allQ_combBytesQ (st : Statement) (c2 : ByteArray) :
    AllQueriesSatisfy (combBytesQ st c2) NoH23 := by
  unfold combBytesQ
  cases st.comb with
  | none => exact allQueriesSatisfy_pure _ _
  | some md => exact allQ_hashQ (by intro h; cases h) _

/-- **Step 2's grinding prefix is computed without `H₂³` queries.** -/
theorem allQ_preGQ (st : Statement) (s : Prover.Pending) (w : ByteArray) :
    AllQueriesSatisfy (preGQ st s w) NoH23 :=
  allQueriesSatisfy_bind (allQ_muDelayedQ _ _) fun _ =>
    allQueriesSatisfy_bind (allQ_hashQ (by decide) _) fun _ =>
    allQueriesSatisfy_bind (allQ_combBytesQ _ _) fun _ => allQueriesSatisfy_pure _ _

end Queries

end VoleMole.ROM.IC
