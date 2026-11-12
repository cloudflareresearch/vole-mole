import VoleMole.ROM.SpecSound

/-!
# The executable verifier as an oracle computation over the hashes and the cipher

The soundness theorems of the random-oracle layer (`ROM/CipherFull.lean`, `ROM/AdaptFull.lean`,
`ROM/SpecSound.lean`) are for a prover `P : OracleComp specIC _` that reaches the hashes and the
ideal cipher only through the oracle `specIC`. The verifier and the extractor of those games read
the cipher table `E` directly (`icPrg E.cipher`). A protocol game in which honest parties verify
proofs *during* the adversary's run (Moussaka's Anchors and Moderator, `ROM/MoussakaOMUF.lean`)
must therefore run the verifier as an oracle computation too, so that the whole game is again a
prover of the soundness theorems. This file builds it.

* `liftIC`: a hash-only computation (`OracleComp spec`) as one over `specIC`; per table it is the
  same computation (`evalWithAnswerFn_liftIC`).
* `prgQ`: the ideal-cipher CTR PRG (`icPrg`) as cipher queries, one per block; `derivNQ`: the BAVC
  tree derivation (`ZK.Sim.derivN`) with its PRG calls as queries.
* `needCells`: the cells the verifier's PRG calls read, computed from the derived tree: the
  derivation's (`children`, 2 blocks per known internal node), the leaf commitments'
  (`leafCom`, 2 blocks) and the VOLE expansion's (`prgWords`, `voleColBlocks` blocks) at every
  leaf of the tree.
* **`verify_congr_cells`**: the verifier with the ideal-cipher PRG reads the table only at those
  cells: two tables that agree there give the same transcript. (`ZK/HopsIC.lean`'s
  `verify_ic_congr` is the same statement at the granularity of whole rows, which an oracle
  computation cannot read.)
* **`verifyIC T st proof`**: query `mu₁` and `iv`, derive the tree with cipher queries, query the
  needed cells, then run `verifyQ` (the verifier with hash queries) with the PRG of the queried
  cells. **`evalWithAnswerFn_verifyIC`**: against complete tables `g` and `E` it is the executable
  verifier with the hashes of `g` and the ideal-cipher PRG of `E`, i.e. what the soundness games'
  own verifier computes.
* Query bounds: `extractorQueries + verifierQueries` per hash kind (`isKindQueryBoundIC_verifyIC`),
  `2 + 337` hash queries (`isQueryBoundP_left_verifyIC`) and `verifyCellBound p` cipher queries
  (`isQueryBoundP_right_verifyIC`; `9212 + 2304·(2 + voleColBlocks)`: the derivation's `4606`
  queries, then the needed cells, the derivation's again among them; so `55292` for Moussaka's
  issuance and `69116` for its redemption, `voleColBlocks` being `18` and `24`).

`treeQ`, `cellsQ` are irreducible wrappers: elaborating a query bound of `derivNQ … 2303` (or of a
`mapM` over `needCells`) otherwise makes Lean evaluate the computation (maximum recursion depth).
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim VoleMole.ROM

variable {α : Type}

/-! ## Hash computations as computations over `specIC` -/

/-- **A hash-only computation over the joint oracle**: every hash query `d` asked as `.inl d`. -/
def liftIC (oa : OracleComp spec α) : OracleComp specIC α :=
  OracleComp.construct (C := fun _ => OracleComp specIC α) (fun a => pure a)
    (fun t _ rec => liftM (specIC.query (.inl t)) >>= fun u => rec u) oa

@[simp] lemma liftIC_pure (a : α) : liftIC (pure a : OracleComp spec α) = pure a := rfl

lemma liftIC_query_bind (d : Dom) (k : Ans d → OracleComp spec α) :
    liftIC (liftM (spec.query d) >>= k) =
      liftM (specIC.query (.inl d)) >>= fun u => liftIC (k u) := rfl

lemma liftIC_bind {β : Type} (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    liftIC (oa >>= ob) = liftIC oa >>= fun a => liftIC (ob a) := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rw [bind_assoc, liftIC_query_bind, liftIC_query_bind, bind_assoc]
    exact congrArg _ (funext fun u => ih u)

/-- **Per table, `liftIC oa` is `oa`.** -/
theorem evalWithAnswerFn_liftIC (g : Table) (E : CTable) (oa : OracleComp spec α) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) (liftIC oa) =
      evalWithAnswerFn (QueryImpl.ofFn g) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rw [liftIC_query_bind]
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply]
    exact ih (g t)

theorem isKindQueryBoundIC_liftIC {oa : OracleComp spec α} {q : Kind → ℕ}
    (h : IsKindQueryBound oa q) : IsKindQueryBoundIC (liftIC oa) q := by
  induction oa using OracleComp.inductionOn generalizing q with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isKindQueryBound_query_bind_iff] at h
    rw [liftIC_query_bind, IsKindQueryBoundIC, isQueryBound_query_bind_iff]
    exact ⟨h.1, fun u => ih u (h.2 u)⟩

theorem isQueryBoundP_right_liftIC (oa : OracleComp spec α) :
    IsQueryBoundP (liftIC oa) (fun t => t.isRight = true) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    rw [liftIC_query_bind, isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp), fun u => by simpa using ih u⟩

theorem isQueryBoundP_left_liftIC {oa : OracleComp spec α} {n : ℕ}
    (h : IsTotalQueryBound oa n) : IsQueryBoundP (liftIC oa) (fun t => t.isLeft = true) n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isTotalQueryBound_query_bind_iff] at h
    rw [liftIC_query_bind, isQueryBoundP_query_bind_iff]
    exact ⟨Or.inr h.1, fun u => by simpa using ih u (h.2 u)⟩

/-! ## The ideal-cipher PRG as cipher queries -/

/-- One cipher cell as a query. -/
def cellQ (x : Cell) : OracleComp specIC Blk := liftM (specIC.query (.inr x))

/-- The cells that `prgR (E k) iv t c n` reads: `(k, ctrBlock iv (c + j) t)` for `j < n`. -/
def ctrCells (k : Blk) (iv : ByteArray) (t c : UInt32) (n : ℕ) : List Cell :=
  (List.range n).map fun j => (k, blk 16 (AES.ctrBlock iv (c + j.toUInt32) t))

/-- **The ideal-cipher PRG with its cells queried** (`icPrgF`): on a 16-byte key, one cipher query
per block; on any other key AES, as `icPrgF`. -/
def prgQ (key iv : ByteArray) (t c : UInt32) (n : ℕ) : OracleComp specIC ByteArray :=
  if key.size = 16 then
    (fun bs : List Blk => (bs.map ba).foldl (· ++ ·) ByteArray.empty) <$>
      (ctrCells (blk 16 key) iv t c n).mapM cellQ
  else pure (AES.prg key iv t c n)

lemma evalWithAnswerFn_mapM {β γ : Type} (f : QueryImpl specIC Id) (l : List β)
    (h : β → OracleComp specIC γ) :
    evalWithAnswerFn f (l.mapM h) = l.map fun x => evalWithAnswerFn f (h x) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.mapM_cons, ih]

@[simp] lemma evalWithAnswerFn_cellQ (g : Table) (E : CTable) (x : Cell) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) (cellQ x) = E x := rfl

theorem evalWithAnswerFn_prgQ (g : Table) (E : CTable) (key iv : ByteArray) (t c : UInt32)
    (n : ℕ) : evalWithAnswerFn (QueryImpl.ofFn (join g E)) (prgQ key iv t c n) =
      @HasPrg.prg (icPrg E.cipher) key iv t c n := by
  show _ = icPrgF E.cipher key iv t c n
  unfold prgQ icPrgF
  split_ifs with hk
  · rw [evalWithAnswerFn_map, evalWithAnswerFn_mapM, prgR_eq_map]
    simp only [ctrCells, List.map_map, Function.comp_def, evalWithAnswerFn_cellQ]
    rfl
  · rfl

/-- **Query bounds compose**: hash queries per kind add up under `>>=`. -/
theorem isKindQueryBoundIC_bind {β : Type} {oa : OracleComp specIC α}
    {ob : α → OracleComp specIC β} {q₁ q₂ : Kind → ℕ} (h₁ : IsKindQueryBoundIC oa q₁)
    (h₂ : ∀ a, IsKindQueryBoundIC (ob a) q₂) : IsKindQueryBoundIC (oa >>= ob) (q₁ + q₂) := by
  refine isQueryBound_bind (combine := (· + ·)) (fun t b₁ b₂ b hb => ?_) (fun t b₁ b₂ b hb => ?_)
    h₁ h₂
  · cases t with
    | inl d => simp only [Pi.add_apply] at hb ⊢; omega
    | inr x => exact ⟨trivial, trivial⟩
  · cases t with
    | inl d =>
      constructor <;> funext k <;> by_cases hk : k = d.1 <;>
        simp [hk, Function.update_of_ne, Pi.add_apply] <;> omega
    | inr x => exact ⟨rfl, rfl⟩

theorem IsKindQueryBoundIC.mono {oa : OracleComp specIC α} {q q' : Kind → ℕ}
    (h : IsKindQueryBoundIC oa q) (hle : q ≤ q') : IsKindQueryBoundIC oa q' := by
  induction oa using OracleComp.inductionOn generalizing q q' with
  | pure a => trivial
  | query_bind t k ih =>
    rw [IsKindQueryBoundIC, isQueryBound_query_bind_iff] at h ⊢
    cases t with
    | inl d =>
      refine ⟨lt_of_lt_of_le h.1 (hle d.1), fun u => ih u (h.2 u) fun k => ?_⟩
      by_cases hk : k = d.1
      · subst hk; simp only [Function.update_self]; exact Nat.sub_le_sub_right (hle _) 1
      · simp only [Function.update_of_ne hk]; exact hle k
    | inr x => exact ⟨trivial, fun u => ih u (h.2 u) hle⟩

theorem isKindQueryBoundIC_map {β : Type} {oa : OracleComp specIC α} (f : α → β)
    {q : Kind → ℕ} (h : IsKindQueryBoundIC oa q) : IsKindQueryBoundIC (f <$> oa) q :=
  (isQueryBound_map_iff _ _ _ _ _).2 h

theorem isKindQueryBoundIC_mapM {β γ : Type} (l : List β) (h : β → OracleComp specIC γ)
    {q : Kind → ℕ} (hh : ∀ x, IsKindQueryBoundIC (h x) q) :
    IsKindQueryBoundIC (l.mapM h) (l.length • q) := by
  induction l with
  | nil => trivial
  | cons x l ih =>
    rw [List.mapM_cons, List.length_cons, succ_nsmul']
    exact isKindQueryBoundIC_bind (hh x) fun a =>
      (by simpa using isKindQueryBoundIC_bind (ob := fun as => (pure (a :: as) :
        OracleComp specIC (List γ))) (q₂ := 0) ih fun _ => trivial)

theorem isQueryBoundP_mapM {β γ : Type} (p : DomIC → Prop) [DecidablePred p] (l : List β)
    (h : β → OracleComp specIC γ) {m : ℕ} (hh : ∀ x, IsQueryBoundP (h x) p m) :
    IsQueryBoundP (l.mapM h) p (l.length * m) := by
  induction l with
  | nil => trivial
  | cons x l ih =>
    rw [List.mapM_cons, List.length_cons, Nat.succ_mul, add_comm]
    exact isQueryBoundP_bind (hh x) fun a _ =>
      (by simpa using isQueryBoundP_bind (ob := fun as => (pure (a :: as) :
        OracleComp specIC (List γ))) (m := 0) ih fun _ _ => isQueryBoundP_pure p _ 0)

theorem isKindQueryBoundIC_cellQ (x : Cell) : IsKindQueryBoundIC (cellQ x) 0 :=
  (isQueryBound_query_iff _ _ _ _).2 trivial

theorem isQueryBoundP_right_cellQ (x : Cell) :
    IsQueryBoundP (cellQ x) (fun t => t.isRight = true) 1 :=
  (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos

theorem isQueryBoundP_left_cellQ (x : Cell) :
    IsQueryBoundP (cellQ x) (fun t => t.isLeft = true) 0 :=
  (isQueryBoundP_query_iff _ _ _).2 fun h => by simp at h

theorem isQueryBoundP_right_prgQ (key iv : ByteArray) (t c : UInt32) (n : ℕ) :
    IsQueryBoundP (prgQ key iv t c n) (fun t => t.isRight = true) n := by
  unfold prgQ
  split_ifs
  · rw [isQueryBoundP_map_iff]
    simpa [ctrCells] using isQueryBoundP_mapM _ (ctrCells (blk 16 key) iv t c n) cellQ
      isQueryBoundP_right_cellQ
  · trivial

theorem isKindQueryBoundIC_prgQ (key iv : ByteArray) (t c : UInt32) (n : ℕ) :
    IsKindQueryBoundIC (prgQ key iv t c n) 0 := by
  unfold prgQ
  split_ifs
  · simpa using isKindQueryBoundIC_map _ (isKindQueryBoundIC_mapM
      (ctrCells (blk 16 key) iv t c n) cellQ isKindQueryBoundIC_cellQ)
  · trivial

theorem isQueryBoundP_left_prgQ (key iv : ByteArray) (t c : UInt32) (n : ℕ) :
    IsQueryBoundP (prgQ key iv t c n) (fun t => t.isLeft = true) 0 := by
  unfold prgQ
  split_ifs
  · rw [isQueryBoundP_map_iff]
    simpa using isQueryBoundP_mapM _ (ctrCells (blk 16 key) iv t c n) cellQ
      isQueryBoundP_left_cellQ
  · trivial

/-! ## The tree derivation with cipher queries -/

/-- `BAVC.deriveStep` with the PRG call as cipher queries. -/
def deriveStepQ (iv : ByteArray) (A : Array (Option ByteArray)) (n : ℕ) :
    OracleComp specIC (Array (Option ByteArray)) :=
  match A[n]! with
  | some node => (fun c => (A.set! (2 * n + 1) (some (BAVC.block c 0))).set! (2 * n + 2)
      (some (BAVC.block c 1))) <$> prgQ node iv n.toUInt32 0 2
  | none => pure A

/-- `ZK.Sim.derivN` (the derivation's first `N` steps) with cipher queries. -/
def derivNQ (iv : ByteArray) (A : Array (Option ByteArray)) : ℕ → OracleComp specIC (Array (Option ByteArray))
  | 0 => pure A
  | N + 1 => derivNQ iv A N >>= fun B => deriveStepQ iv B N

theorem evalWithAnswerFn_deriveStepQ (g : Table) (E : CTable) (iv : ByteArray)
    (A : Array (Option ByteArray)) (n : ℕ) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) (deriveStepQ iv A n) =
      @BAVC.deriveStep (icPrg E.cipher) iv A n := by
  unfold deriveStepQ BAVC.deriveStep
  rcases hA : A[n]! with _ | node
  · rfl
  · simp only [evalWithAnswerFn_map, evalWithAnswerFn_prgQ]; rfl

theorem evalWithAnswerFn_derivNQ (g : Table) (E : CTable) (iv : ByteArray)
    (A : Array (Option ByteArray)) (N : ℕ) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) (derivNQ iv A N) =
      @derivN (icPrg E.cipher) iv A N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [derivNQ, evalWithAnswerFn_bind, ih, evalWithAnswerFn_deriveStepQ, @derivN_succ (icPrg E.cipher)]

theorem isKindQueryBoundIC_derivNQ (iv : ByteArray) (A : Array (Option ByteArray)) (N : ℕ) :
    IsKindQueryBoundIC (derivNQ iv A N) 0 := by
  induction N with
  | zero => trivial
  | succ N ih =>
    refine (isKindQueryBoundIC_bind (q₂ := 0) ih fun B => ?_).mono (by simp)
    unfold deriveStepQ
    split
    · exact isKindQueryBoundIC_map _ (isKindQueryBoundIC_prgQ _ _ _ _ _)
    · trivial

theorem isQueryBoundP_right_derivNQ (iv : ByteArray) (A : Array (Option ByteArray)) (N : ℕ) :
    IsQueryBoundP (derivNQ iv A N) (fun t => t.isRight = true) (2 * N) := by
  induction N with
  | zero => trivial
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 2 by ring]
    refine isQueryBoundP_bind ih fun B _ => ?_
    unfold deriveStepQ
    split
    · exact (isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_right_prgQ _ _ _ _ _)
    · trivial

theorem isQueryBoundP_left_derivNQ (iv : ByteArray) (A : Array (Option ByteArray)) (N : ℕ) :
    IsQueryBoundP (derivNQ iv A N) (fun t => t.isLeft = true) 0 := by
  induction N with
  | zero => trivial
  | succ N ih =>
    refine isQueryBoundP_bind (m := 0) ih fun B _ => ?_
    unfold deriveStepQ
    split
    · exact (isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_left_prgQ _ _ _ _ _)
    · trivial

/-! ## The cells the verifier reads -/

/-- The cells of one PRG call, if its key is a 16-byte block (otherwise AES answers it). -/
def callCells (key iv : ByteArray) (t c : UInt32) (n : ℕ) : List Cell :=
  if key.size = 16 then ctrCells (blk 16 key) iv t c n else []

/-- **The cells the verifier reads**, from the derived tree `A`: the derivation's PRG calls at the
known internal nodes, and the leaf commitments' and the VOLE expansion's PRG calls at every leaf
position of the tree (the hidden leaves included: an over-approximation). -/
def needCells (p : Params) (iv : ByteArray) (A : Array (Option ByteArray)) : List Cell :=
  ((List.range (BAVC.numLeaves - 1)).flatMap fun n => match A[n]! with
    | some node => callCells node iv n.toUInt32 0 2
    | none => []) ++
  ((List.range BAVC.tau).flatMap fun i => (List.range (2 ^ BAVC.kOf i)).flatMap fun j =>
    let key := (A.map (·.getD BAVC.zeroBlock))[BAVC.treePos i j]!
    callCells key iv (i + BAVC.numLeaves - 1).toUInt32 0 2 ++
      callCells key iv (((1 : UInt32) <<< 31) + i.toUInt32) 0 p.voleColBlocks)

/-- Two tables that agree at a call's cells give the PRG the same output there. -/
theorem icPrgF_congr_cells {E E' : Cipher} {key iv : ByteArray} {t c : UInt32} {n : ℕ}
    (h : ∀ x ∈ callCells key iv t c n, E x.1 x.2 = E' x.1 x.2) :
    @HasPrg.prg (icPrg E) key iv t c n = @HasPrg.prg (icPrg E') key iv t c n := by
  show icPrgF E key iv t c n = icPrgF E' key iv t c n
  unfold icPrgF
  split_ifs with hk
  · rw [prgR_eq_map, prgR_eq_map]
    congr 1
    refine List.map_congr_left fun j hj => ?_
    have := h (blk 16 key, blk 16 (AES.ctrBlock iv (c + j.toUInt32) t)) (by
      simp only [callCells, hk, ite_true, ctrCells, List.mem_map]
      exact ⟨j, hj, rfl⟩)
    rw [this]
  · rfl

section Congr

variable {E E' : Cipher} {p : Params} {iv opening delta : ByteArray}

/-- `needCells` at the final derivation with `E`. -/
abbrev cellsE (E : Cipher) (p : Params) (iv opening delta : ByteArray) : List Cell :=
  needCells p iv (@derivedN (icPrg E) iv opening delta (BAVC.numLeaves - 1))

theorem derivedN_congr_cells (h : ∀ x ∈ cellsE E p iv opening delta, E x.1 x.2 = E' x.1 x.2) :
    ∀ N ≤ BAVC.numLeaves - 1,
      @derivedN (icPrg E) iv opening delta N = @derivedN (icPrg E') iv opening delta N := by
  intro N
  induction N with
  | zero => intro _; exact (@derivN_zero (icPrg E) iv _).trans (@derivN_zero (icPrg E') iv _).symm
  | succ N ih =>
    intro hN
    rewrite [@derivedN_succ (icPrg E), @derivedN_succ (icPrg E'), ← ih (by omega)]
    rcases hA : (@derivedN (icPrg E) iv opening delta N)[N]! with _ | node
    · simp only [BAVC.deriveStep, hA]
    · have hc : @BAVC.children (icPrg E) iv node N = @BAVC.children (icPrg E') iv node N := by
        refine icPrgF_congr_cells fun x hx => h x ?_
        simp only [cellsE, needCells, List.mem_append, List.mem_flatMap, List.mem_range]
        refine Or.inl ⟨N, by omega, ?_⟩
        rw [@derivedN_stable (icPrg E) iv opening delta N _ (by omega), hA]
        exact hx
      simp only [BAVC.deriveStep, hA, hc]

theorem recTree_congr_cells (h : ∀ x ∈ cellsE E p iv opening delta, E x.1 x.2 = E' x.1 x.2) :
    @recTree (icPrg E) iv opening delta = @recTree (icPrg E') iv opening delta := by
  unfold recTree
  rw [derivedN_congr_cells h _ le_rfl]

lemma mem_cellsE_leaf {i j : ℕ} (hi : i < BAVC.tau) (hj : j < 2 ^ BAVC.kOf i) {x : Cell}
    (hx : x ∈ callCells (@recTree (icPrg E) iv opening delta)[BAVC.treePos i j]! iv
        (i + BAVC.numLeaves - 1).toUInt32 0 2 ∨
      x ∈ callCells (@recTree (icPrg E) iv opening delta)[BAVC.treePos i j]! iv
        (((1 : UInt32) <<< 31) + i.toUInt32) 0 p.voleColBlocks) :
    x ∈ cellsE E p iv opening delta := by
  simp only [cellsE, needCells, List.mem_append, List.mem_flatMap, List.mem_range]
  exact Or.inr ⟨i, hi, j, hj, hx⟩

theorem reconstruct_congr_cells (h : ∀ x ∈ cellsE E p iv opening delta, E x.1 x.2 = E' x.1 x.2) :
    @BAVC.reconstruct (icPrg E) iv opening delta = @BAVC.reconstruct (icPrg E') iv opening delta := by
  have ht := recTree_congr_cells h
  rewrite [@reconstruct_eq (icPrg E), @reconstruct_eq (icPrg E'), ← ht]
  split_ifs with hb
  · rfl
  · rewrite [@leavesOf_eq (icPrg E), @leavesOf_eq (icPrg E')]
    simp only [Option.some.injEq, BAVC.Leaves.mk.injEq, true_and]
    apply congrArg (List.foldl (· ++ ·) ByteArray.empty)
    refine pieces_congr fun i hi j hj => ?_
    split_ifs
    · rfl
    · exact icPrgF_congr_cells fun x hx => h x (mem_cellsE_leaf hi hj (Or.inl hx))

/-- The VOLE expansion with two PRGs that agree at its calls (the non-hidden leaves' keys). -/
theorem convertToVoleAt_congr_cells {pr : Params} {dbit : ℕ → Bool} {corr : ℕ → ByteArray}
    {iv' : ByteArray} {key : ℕ → ℕ → ByteArray}
    (h : ∀ i < BAVC.tau, ∀ j < 2 ^ BAVC.kOf i, j ≠ BAVC.hiddenIndex dbit i →
      @HasPrg.prg (icPrg E) (key i j) iv' (((1 : UInt32) <<< 31) + i.toUInt32) 0 pr.voleColBlocks =
        @HasPrg.prg (icPrg E') (key i j) iv' (((1 : UInt32) <<< 31) + i.toUInt32) 0
          pr.voleColBlocks) :
    @convertToVoleAt (icPrg E) pr dbit corr iv' key = @convertToVoleAt (icPrg E') pr dbit corr iv' key := by
  have ht : ∀ i < BAVC.tau,
      @treeColumns (icPrg E) pr iv' i (BAVC.hiddenIndex dbit i) (corr i) (key i) =
      @treeColumns (icPrg E') pr iv' i (BAVC.hiddenIndex dbit i) (corr i) (key i) := by
    intro i hi
    have hp : @prgOuts (icPrg E) pr iv' i (BAVC.hiddenIndex dbit i) (key i) =
        @prgOuts (icPrg E') pr iv' i (BAVC.hiddenIndex dbit i) (key i) := by
      unfold prgOuts
      refine Array.map_congr_left fun j hj => ?_
      have hj := Array.mem_range.1 hj
      split_ifs with hjd
      · rfl
      · simp only [prgWords]
        rw [h i hi j hj (by simpa using hjd)]
    simp only [treeColumns, hp]
  have htr : ((Array.range BAVC.tau).map fun i =>
      @treeColumns (icPrg E) pr iv' i (BAVC.hiddenIndex dbit i) (corr i) (key i)) =
      (Array.range BAVC.tau).map fun i =>
        @treeColumns (icPrg E') pr iv' i (BAVC.hiddenIndex dbit i) (corr i) (key i) :=
    Array.map_congr_left fun i hi => ht i (Array.mem_range.1 hi)
  simp only [convertToVoleAt, htr]

/-- **The verifier with the ideal-cipher PRG reads the table only at `cellsE`**: two tables that
agree at the cells of its PRG calls (computed from its own derivation) give the same transcript. -/
theorem verify_congr_cells (Hs : Hashes) (T : CrtTables) (st : Statement) (proof : ByteArray)
    (h : ∀ x ∈ cellsE E st.params (ivOf Hs ⟨st.params, proof⟩ (st.mu1 Hs))
      (⟨st.params, proof⟩ : Proof).opening (⟨st.params, proof⟩ : Proof).delta,
      E x.1 x.2 = E' x.1 x.2) :
    @verify (icPrg E) Hs T st proof = @verify (icPrg E') Hs T st proof := by
  set pf : Proof := ⟨st.params, proof⟩ with hpf
  have hr := reconstruct_congr_cells h
  simp only [verify, Id.run]
  rw [← hpf, ← hr]
  split
  · rfl
  · split
    · rename_i leaves hl
      have hc : @convertToVole (icPrg E) pf (ivOf Hs pf (st.mu1 Hs)) leaves =
          @convertToVole (icPrg E') pf (ivOf Hs pf (st.mu1 Hs)) leaves := by
        unfold convertToVole
        refine convertToVoleAt_congr_cells fun i hi j hj hjd => ?_
        rw [@leafKey_reconstruct (icPrg E) _ _ _ leaves hl i j hi hj hjd]
        exact icPrgF_congr_cells fun x hx => h x (mem_cellsE_leaf hi hj (Or.inr hx))
      rw [hc]
    · rfl

end Congr

/-! ## The verifier as an oracle computation -/

/-- **The PRG table of the queried cells**: each queried cell's answer, zero elsewhere. -/
def fillC (M : List (Cell × Blk)) : Cipher := fun k z => (M.lookup (k, z)).getD 0

lemma lookup_map_self (E : CTable) {l : List Cell} {x : Cell} (hx : x ∈ l) :
    (l.map fun y => (y, E y)).lookup x = some (E x) := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    simp only [List.map_cons, List.lookup_cons]
    by_cases hxy : x = y
    · subst hxy; simp
    · have : (x == y) = false := by simpa using hxy
      rw [this]
      exact ih (by simpa [hxy] using hx)

/-- `mu₁` and then `iv`, as hash queries (the start of `verifyQ`, and the extractor's queries). -/
def ivQ (st : Statement) (proof : ByteArray) : OracleComp spec ByteArray := do
  let mu1 ← mu1Q st
  hashQ .h4 (((⟨st.params, proof⟩ : Proof).ivPre ++ mu1).push 4)

@[simp] lemma evalWithAnswerFn_ivQ (g : Table) (st : Statement) (proof : ByteArray) :
    evalWithAnswerFn (QueryImpl.ofFn g) (ivQ st proof) =
      ivOf (Hashes.ofTable g) ⟨st.params, proof⟩ (st.mu1 (Hashes.ofTable g)) := by
  simp [ivQ, ivOf]

theorem isKindQueryBound_ivQ (st : Statement) (proof : ByteArray) :
    IsKindQueryBound (ivQ st proof) extractorQueries := by
  have h4 : ∀ k : Kind, k ≠ .h4 → ∀ mu1 : ByteArray,
      IsKindQueryBound (hashQ .h4 (((⟨st.params, proof⟩ : Proof).ivPre ++ mu1).push 4))
        (Function.update extractorQueries k (extractorQueries k - 1)) := by
    intro k hk mu1
    have := (isKindQueryBound_hashQ_bind_iff (k := .h4) (x := (((⟨st.params, proof⟩ : Proof).ivPre ++ mu1).push 4))
      (f := fun u => (pure u : OracleComp spec ByteArray))
      (q := Function.update extractorQueries k (extractorQueries k - 1))).2
      ⟨by rw [Function.update_of_ne (Ne.symm hk)]; simp [extractorQueries], fun _ => trivial⟩
    simpa using this
  unfold ivQ mu1Q
  split
  · exact isKindQueryBound_hashQ_bind_iff.2 ⟨by simp [extractorQueries], fun u =>
      h4 .muDelayed (by decide) u.ba⟩
  · exact isKindQueryBound_hashQ_bind_iff.2 ⟨by simp [extractorQueries], fun u =>
      h4 .mu (by decide) u.ba⟩

theorem isTotalQueryBound_ivQ (st : Statement) (proof : ByteArray) :
    IsTotalQueryBound (ivQ st proof) 2 := by
  unfold ivQ mu1Q hashQ
  split <;> simp only [bind_map_left] <;>
    exact isTotalQueryBound_query_bind_iff.2 ⟨by omega, fun u =>
      (isQueryBound_map_iff _ _ _ _ _).2 ((isQueryBound_query_iff _ _ _ _).2 Nat.one_pos)⟩

/-- **The derived tree** of an opening, with cipher queries (`derivNQ` from the placed seeds, all
`L − 1` steps). Irreducible: unification must not unfold the `2303` steps. -/
@[irreducible] def treeQ (iv opening delta : ByteArray) : OracleComp specIC (Array (Option ByteArray)) :=
  derivNQ iv (placedOf opening delta) (BAVC.numLeaves - 1)

theorem evalWithAnswerFn_treeQ (g : Table) (E : CTable) (iv opening delta : ByteArray) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) (treeQ iv opening delta) =
      @derivedN (icPrg E.cipher) iv opening delta (BAVC.numLeaves - 1) := by
  unfold treeQ derivedN
  generalize BAVC.numLeaves - 1 = N
  exact evalWithAnswerFn_derivNQ g E iv _ N

theorem isKindQueryBoundIC_treeQ (iv opening delta : ByteArray) :
    IsKindQueryBoundIC (treeQ iv opening delta) 0 := by
  unfold treeQ; generalize BAVC.numLeaves - 1 = N; exact isKindQueryBoundIC_derivNQ iv (placedOf opening delta) N

theorem isQueryBoundP_right_treeQ (iv opening delta : ByteArray) :
    IsQueryBoundP (treeQ iv opening delta) (fun t => t.isRight = true)
      (2 * (BAVC.numLeaves - 1)) := by
  unfold treeQ; generalize BAVC.numLeaves - 1 = N
  exact isQueryBoundP_right_derivNQ iv (placedOf opening delta) N

theorem isQueryBoundP_left_treeQ (iv opening delta : ByteArray) :
    IsQueryBoundP (treeQ iv opening delta) (fun t => t.isLeft = true) 0 := by
  unfold treeQ; generalize BAVC.numLeaves - 1 = N; exact isQueryBoundP_left_derivNQ iv (placedOf opening delta) N

/-- **The needed cells, queried** (with their answers). Irreducible, as `treeQ`. -/
@[irreducible] def cellsQ (p : Params) (iv : ByteArray) (A : Array (Option ByteArray)) :
    OracleComp specIC (List (Cell × Blk)) :=
  (needCells p iv A).mapM fun x => (fun v => (x, v)) <$> cellQ x

theorem evalWithAnswerFn_cellsQ (g : Table) (E : CTable) (p : Params) (iv : ByteArray)
    (A : Array (Option ByteArray)) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) (cellsQ p iv A) =
      (needCells p iv A).map fun x => (x, E x) := by
  unfold cellsQ
  generalize needCells p iv A = l
  rw [evalWithAnswerFn_mapM]
  simp only [evalWithAnswerFn_map, evalWithAnswerFn_cellQ]

/-- **The executable verifier as an oracle computation over the hashes and the cipher**: the
hashes `mu₁`, `iv`; the tree derivation with cipher queries (`derivNQ`); the cells the verifier
reads (`needCells`), queried; then `verifyQ` (hash queries) with the ideal-cipher PRG of the
queried cells (`fillC`). -/
def verifyIC (T : CrtTables) (st : Statement) (proof : ByteArray) : OracleComp specIC Transcript := do
  let pf : Proof := ⟨st.params, proof⟩
  let iv ← liftIC (ivQ st proof)
  let A ← treeQ iv pf.opening pf.delta
  let M ← cellsQ st.params iv A
  liftIC (@verifyQ (icPrg (fillC M)) T st proof)

/-- **Per table, `verifyIC` is the executable verifier** with the hashes of `g` and the
ideal-cipher PRG of `E`: what the soundness games' own verifier (`gameIC`, `gameA`) computes. -/
theorem evalWithAnswerFn_verifyIC (g : Table) (E : CTable) (T : CrtTables) (st : Statement)
    (proof : ByteArray) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) (verifyIC T st proof) =
      @verify (icPrg E.cipher) (Hashes.ofTable g) T st proof := by
  simp only [verifyIC, evalWithAnswerFn_bind, evalWithAnswerFn_liftIC, evalWithAnswerFn_ivQ,
    evalWithAnswerFn_treeQ, evalWithAnswerFn_verifyQ]
  rw [evalWithAnswerFn_cellsQ]
  refine (verify_congr_cells (Hashes.ofTable g) T st proof fun x hx => ?_).symm
  show E x = (_ : Option Blk).getD 0
  erw [lookup_map_self E hx]
  rfl

/-! ## Query bounds of `verifyIC` -/

lemma length_flatMap_le_sum {β γ : Type} (l : List β) (f : β → List γ) (c : β → ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ c a) : (l.flatMap f).length ≤ (l.map c).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

lemma length_callCells_le (key iv : ByteArray) (t c : UInt32) (n : ℕ) :
    (callCells key iv t c n).length ≤ n := by
  unfold callCells
  split_ifs <;> simp [ctrCells]

theorem sum_leaves : ((List.range BAVC.tau).map fun i => 2 ^ BAVC.kOf i).sum = BAVC.numLeaves := by
  decide

/-- At most `2(L − 1) + L·(2 + voleColBlocks)` cells. -/
theorem length_needCells_le (p : Params) (iv : ByteArray) (A : Array (Option ByteArray)) :
    (needCells p iv A).length ≤
      2 * (BAVC.numLeaves - 1) + BAVC.numLeaves * (2 + p.voleColBlocks) := by
  unfold needCells
  rw [List.length_append]
  refine Nat.add_le_add ?_ ?_
  · refine (length_flatMap_le_sum _ _ (fun _ => 2) fun n _ => ?_).trans (by simp [mul_comm])
    split
    · exact length_callCells_le _ _ _ _ _
    · simp
  · refine (length_flatMap_le_sum _ _ (fun i => 2 ^ BAVC.kOf i * (2 + p.voleColBlocks))
      fun i _ => ?_).trans (le_of_eq ?_)
    · refine (length_flatMap_le_sum _ _ (fun _ => 2 + p.voleColBlocks) fun j _ => ?_).trans
        (by simp)
      rw [List.length_append]
      exact Nat.add_le_add (length_callCells_le _ _ _ _ _) (length_callCells_le _ _ _ _ _)
    · rw [List.sum_map_mul_right, sum_leaves]

/-- **The cipher queries of one verification**: the derivation's and the needed cells'. -/
def verifyCellBound (p : Params) : ℕ :=
  2 * (BAVC.numLeaves - 1) + (2 * (BAVC.numLeaves - 1) + BAVC.numLeaves * (2 + p.voleColBlocks))

theorem verifyCellBound_eq (p : Params) : verifyCellBound p = 9212 + 2304 * (2 + p.voleColBlocks) := by
  simp only [verifyCellBound, BAVC.numLeaves]; omega

-- `derivNQ … (numLeaves − 1)` must not be unfolded by unification (2303 steps).

theorem isKindQueryBoundIC_mapM_zero {β γ : Type} (l : List β) (h : β → OracleComp specIC γ)
    (hh : ∀ x, IsKindQueryBoundIC (h x) 0) : IsKindQueryBoundIC (l.mapM h) 0 := by
  simpa using isKindQueryBoundIC_mapM l h hh

theorem isQueryBoundP_mapM_zero {β γ : Type} (p : DomIC → Prop) [DecidablePred p] (l : List β)
    (h : β → OracleComp specIC γ) (hh : ∀ x, IsQueryBoundP (h x) p 0) :
    IsQueryBoundP (l.mapM h) p 0 := by
  simpa using isQueryBoundP_mapM p l h hh

theorem isKindQueryBoundIC_cellsQ (p : Params) (iv : ByteArray) (A : Array (Option ByteArray)) :
    IsKindQueryBoundIC (cellsQ p iv A) 0 := by
  unfold cellsQ
  generalize needCells p iv A = l
  exact isKindQueryBoundIC_mapM_zero _ _ fun x => isKindQueryBoundIC_map _ (isKindQueryBoundIC_cellQ x)

theorem isQueryBoundP_left_cellsQ (p : Params) (iv : ByteArray) (A : Array (Option ByteArray)) :
    IsQueryBoundP (cellsQ p iv A) (fun t => t.isLeft = true) 0 := by
  unfold cellsQ
  generalize needCells p iv A = l
  exact isQueryBoundP_mapM_zero _ _ _ fun x =>
    (isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_left_cellQ x)

theorem isQueryBoundP_right_cellsQ (p : Params) (iv : ByteArray) (A : Array (Option ByteArray)) :
    IsQueryBoundP (cellsQ p iv A) (fun t => t.isRight = true)
      (2 * (BAVC.numLeaves - 1) + BAVC.numLeaves * (2 + p.voleColBlocks)) := by
  unfold cellsQ
  have hl := length_needCells_le p iv A
  generalize needCells p iv A = l at hl ⊢
  generalize 2 * (BAVC.numLeaves - 1) + BAVC.numLeaves * (2 + p.voleColBlocks) = n at hl ⊢
  exact (isQueryBoundP_mapM _ _ _ fun x =>
    (isQueryBoundP_map_iff _ _ _).2 (isQueryBoundP_right_cellQ x)).mono (by simpa using hl)

theorem isKindQueryBoundIC_verifyIC (T : CrtTables) (st : Statement) (proof : ByteArray) :
    IsKindQueryBoundIC (verifyIC T st proof) (extractorQueries + verifierQueries) := by
  unfold verifyIC
  refine isKindQueryBoundIC_bind (isKindQueryBoundIC_liftIC (isKindQueryBound_ivQ st proof))
    fun iv => ?_
  refine (isKindQueryBoundIC_bind (q₁ := 0) (q₂ := verifierQueries)
    (isKindQueryBoundIC_treeQ _ _ _) fun A => ?_).mono (by simp only [zero_add, le_refl])
  refine (isKindQueryBoundIC_bind (q₁ := 0) (q₂ := verifierQueries)
    (isKindQueryBoundIC_cellsQ _ _ _) fun M => ?_).mono (by simp only [zero_add, le_refl])
  exact isKindQueryBoundIC_liftIC (@isKindQueryBound_verifyQ (icPrg (fillC M)) T st proof)

theorem isQueryBoundP_left_verifyIC (T : CrtTables) (st : Statement) (proof : ByteArray) :
    IsQueryBoundP (verifyIC T st proof) (fun t => t.isLeft = true) (2 + verifierTotal) := by
  unfold verifyIC
  refine isQueryBoundP_bind (isQueryBoundP_left_liftIC (isTotalQueryBound_ivQ st proof))
    fun iv _ => ?_
  refine (isQueryBoundP_bind (n := 0) (m := verifierTotal) (isQueryBoundP_left_treeQ _ _ _)
    fun A _ => ?_).mono (by simp only [zero_add, le_refl])
  refine (isQueryBoundP_bind (n := 0) (m := verifierTotal) (isQueryBoundP_left_cellsQ _ _ _)
    fun M _ => ?_).mono
      (by simp only [zero_add, le_refl])
  exact isQueryBoundP_left_liftIC (@isTotalQueryBound_verifyQ (icPrg (fillC M)) T st proof)

theorem isQueryBoundP_right_verifyIC (T : CrtTables) (st : Statement) (proof : ByteArray) :
    IsQueryBoundP (verifyIC T st proof) (fun t => t.isRight = true) (verifyCellBound st.params) := by
  unfold verifyIC
  refine (isQueryBoundP_bind (n := 0) (m := verifyCellBound st.params)
    (isQueryBoundP_right_liftIC (ivQ st proof)) fun iv _ => ?_).mono (by simp only [zero_add, le_refl])
  refine isQueryBoundP_bind (n := 2 * (BAVC.numLeaves - 1)) (isQueryBoundP_right_treeQ _ _ _)
    fun A _ => ?_
  exact (isQueryBoundP_bind (m := 0) (isQueryBoundP_right_cellsQ _ _ _) fun M _ =>
      isQueryBoundP_right_liftIC _).mono (by simp only [add_zero, le_refl])

end VoleMole.ROM.IC
