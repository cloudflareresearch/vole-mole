import VoleMole.ROM.ExtractReduce

/-!
# The executable verifier with the cipher as queries (`VerifierIC`)

The executable verifier (`Verifier.verify`) reads the cipher through its PRG (`icPrg E.cipher`
against a cipher table `E`). A party that verifies inside a prover of the extraction game
(`ROM/ExtractReduce.lean`, `proverAt`) must make those reads as queries to the cipher, so that the
straight-line extractor sees them. This file writes that verifier, `verifyIC`, as a VCVio
computation against the hashes and the cipher (`specIC`), and proves `VerifierIC` for it:

* `evalWithAnswerFn_verifyIC`: against the tables `g` (hashes) and `E` (cipher), `verifyIC` is the
  executable verifier with the ideal-cipher PRG of `E`;
* its queries: per kind those of `verifyQ` (`verifierQueries`), `verifierTotal` hash queries in
  all, and at most `cipherCount p` cipher queries for a statement with parameters `p`.

The CTR PRG (`prgIC`) makes one cipher query per block at a 16-byte key; the BAVC reconstruction
(`reconstructIC`: the GGM derivation, `deriveStepIC`, and the leaf commitments, `leavesOfIC`) and
the VOLE expansion (`convertToVoleIC`) call it where the executable code calls `HasPrg.prg`; the
rest is `verifyQ` with its hash queries lifted (`liftH`).
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Verifier VoleMole.ROM VoleMole.ZK.Sim

/-! ## Evaluation through loops -/

section Loops

variable {ι' : Type} {sp : OracleSpec ι'} (f : QueryImpl sp Id) {α β : Type}

theorem evalWithAnswerFn_foldlM (h : β → α → OracleComp sp β) (l : List α) (b : β) :
    evalWithAnswerFn f (l.foldlM h b) = l.foldl (fun b a => evalWithAnswerFn f (h b a)) b := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih => simp only [List.foldlM_cons, evalWithAnswerFn_bind, ih, List.foldl_cons]

theorem evalWithAnswerFn_forIn_list (l : List α) (b : β)
    (body : α → β → OracleComp sp (ForInStep β)) :
    evalWithAnswerFn f (forIn l b body) =
      forIn (m := Id) l b (fun a b => evalWithAnswerFn f (body a b)) := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih =>
    rw [List.forIn_cons, List.forIn_cons, evalWithAnswerFn_bind]
    cases evalWithAnswerFn f (body a b) with
    | done b' => rfl
    | yield b' => exact ih b'

theorem evalWithAnswerFn_forIn_range (r : Std.Legacy.Range) (b : β)
    (body : ℕ → β → OracleComp sp (ForInStep β)) :
    evalWithAnswerFn f (forIn r b body) =
      forIn (m := Id) r b (fun a b => evalWithAnswerFn f (body a b)) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  exact evalWithAnswerFn_forIn_list f _ _ _

theorem evalWithAnswerFn_arrayMapM (h : α → OracleComp sp β) (xs : Array α) :
    evalWithAnswerFn f (xs.mapM h) = xs.map fun a => evalWithAnswerFn f (h a) := by
  rw [Array.mapM_eq_mapM_toList, evalWithAnswerFn_map, evalWithAnswerFn_mapM]
  apply Array.ext'
  simp

end Loops


/-! ## Query bounds through loops -/

section LoopBounds

variable {ι' : Type} {sp : OracleSpec ι'} (p : ι' → Prop) [DecidablePred p] {α β : Type}

theorem isQueryBoundP_foldlM {h : β → α → OracleComp sp β} {c : ℕ}
    (hc : ∀ b a, IsQueryBoundP (h b a) p c) (l : List α) (b : β) :
    IsQueryBoundP (l.foldlM h b) p (l.length * c) := by
  induction l generalizing b with
  | nil => trivial
  | cons a l ih =>
    rw [List.foldlM_cons, List.length_cons, Nat.succ_mul, Nat.add_comm]
    exact isQueryBoundP_bind (hc b a) fun b' _ => ih b'

theorem isQueryBoundP_forIn_list {body : α → β → OracleComp sp (ForInStep β)} {c : ℕ}
    (hc : ∀ a b, IsQueryBoundP (body a b) p c) (l : List α) (b : β) :
    IsQueryBoundP (forIn l b body) p (l.length * c) := by
  induction l generalizing b with
  | nil => trivial
  | cons a l ih =>
    rw [List.forIn_cons, List.length_cons, Nat.succ_mul, Nat.add_comm]
    refine isQueryBoundP_bind (hc a b) fun r _ => ?_
    cases r with
    | done b' => exact isQueryBoundP_pure p _ _
    | yield b' => exact ih b'

theorem isQueryBoundP_forIn_range {body : ℕ → β → OracleComp sp (ForInStep β)} {c : ℕ}
    (hc : ∀ a b, IsQueryBoundP (body a b) p c) (n : ℕ) (b : β) :
    IsQueryBoundP (forIn [0:n] b body) p (n * c) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have := isQueryBoundP_forIn_list p hc (List.range' 0 [0:n].size [0:n].step) b
  simpa [Std.Legacy.Range.size] using this

theorem isQueryBoundP_listMapM {h : α → OracleComp sp β} {c : ℕ}
    (hc : ∀ a, IsQueryBoundP (h a) p c) (l : List α) :
    IsQueryBoundP (l.mapM h) p (l.length * c) := by
  induction l with
  | nil => trivial
  | cons a l ih =>
    rw [List.mapM_cons, List.length_cons, Nat.succ_mul, Nat.add_comm]
    exact isQueryBoundP_bind (hc a) fun b _ =>
      isQueryBoundP_bind (m := 0) ih fun _ _ => isQueryBoundP_pure p _ 0

theorem isQueryBoundP_arrayMapM {h : α → OracleComp sp β} {c : ℕ}
    (hc : ∀ a, IsQueryBoundP (h a) p c) (xs : Array α) :
    IsQueryBoundP (xs.mapM h) p (xs.size * c) := by
  rw [Array.mapM_eq_mapM_toList, IsQueryBoundP, isQueryBound_map_iff]
  have := isQueryBoundP_listMapM p hc xs.toList
  rw [Array.length_toList] at this
  exact this

end LoopBounds

/-! ## The PRG and the BAVC reconstruction -/

/-- One cipher query, as a block. -/
def cipherQ (k z : Blk) : OracleComp specIC Blk :=
  (liftM (specIC.query (.inr (k, z))) : OracleComp specIC Blk)

/-- **The CTR PRG with the cipher as queries**: block `j` is the cipher at the key and the
`j`-th counter block; a key of another length is answered by AES, as `icPrgF` does. -/
def prgIC (key iv : ByteArray) (t c : UInt32) (n : ℕ) : OracleComp specIC ByteArray :=
  if key.size = 16 then
    (List.range n).foldlM (fun out j =>
      (fun y => out ++ ba y) <$> cipherQ (blk 16 key) (blk 16 (AES.ctrBlock iv (c + j.toUInt32) t)))
      ByteArray.empty
  else pure (AES.prg key iv t c n)

theorem evalWithAnswerFn_prgIC (g : Table) (E : CTable) (key iv : ByteArray) (t c : UInt32)
    (n : ℕ) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) (prgIC key iv t c n) =
      icPrgF E.cipher key iv t c n := by
  unfold prgIC icPrgF
  split
  · rw [evalWithAnswerFn_foldlM]; rfl
  · rfl

/-- `BAVC.deriveStep` with the cipher as queries. -/
def deriveStepIC (iv : ByteArray) (known : Array (Option ByteArray)) (n : ℕ) :
    OracleComp specIC (Array (Option ByteArray)) :=
  match known[n]! with
  | some node => do
    let c ← prgIC node iv n.toUInt32 0 2
    pure ((known.set! (2 * n + 1) (some (BAVC.block c 0))).set! (2 * n + 2) (some (BAVC.block c 1)))
  | none => pure known

theorem evalWithAnswerFn_deriveStepIC (g : Table) (E : CTable) (iv : ByteArray)
    (known : Array (Option ByteArray)) (n : ℕ) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) (deriveStepIC iv known n) =
      @BAVC.deriveStep (icPrg E.cipher) iv known n := by
  unfold deriveStepIC BAVC.deriveStep
  cases h : known[n]! with
  | none => rfl
  | some node => simp only [evalWithAnswerFn_bind, evalWithAnswerFn_prgIC, evalWithAnswerFn_pure]; rfl

/-- `BAVC.leavesOf` with the cipher as queries. -/
def leavesOfIC (iv : ByteArray) (t : Array ByteArray) (hidden : Nat → Option Nat)
    (hiddenCom : Nat → ByteArray) : OracleComp specIC BAVC.Leaves := do
  let mut keys := ByteArray.emptyWithCapacity (16 * BAVC.numLeaves)
  let mut coms := ByteArray.emptyWithCapacity (BAVC.hashLen * BAVC.numLeaves)
  for i in [0:BAVC.tau] do
    for j in [0:2 ^ BAVC.kOf i] do
      if hidden i == some j then
        keys := keys ++ BAVC.zeroBlock
        coms := coms ++ hiddenCom i
      else
        let key := t[BAVC.treePos i j]!
        keys := keys ++ key
        let lc ← prgIC key iv (i + BAVC.numLeaves - 1).toUInt32 0 2
        coms := coms ++ lc
  return ⟨keys, coms⟩

theorem evalWithAnswerFn_leavesOfIC (g : Table) (E : CTable) (iv : ByteArray)
    (t : Array ByteArray) (hidden : Nat → Option Nat) (hiddenCom : Nat → ByteArray) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) (leavesOfIC iv t hidden hiddenCom) =
      @BAVC.leavesOf (icPrg E.cipher) iv t hidden hiddenCom := by
  unfold leavesOfIC BAVC.leavesOf
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_forIn_range, evalWithAnswerFn_pure,
    apply_ite (evalWithAnswerFn _), evalWithAnswerFn_prgIC, BAVC.leafCom]
  rfl

/-- **`BAVC.reconstruct` with the cipher as queries.** -/
def reconstructIC (iv opening delta : ByteArray) : OracleComp specIC (Option BAVC.Leaves) :=
  let nodes := BAVC.openNodes delta
  let seedsEnd := BAVC.tau * BAVC.hashLen + 16 * nodes.size
  if opening.size != BAVC.openSize || seedsEnd > BAVC.openSize ||
      (List.range (BAVC.openSize - seedsEnd)).any fun k => opening.get! (seedsEnd + k) != 0 then
    pure none
  else do
    let placed := (List.range nodes.size).foldl (fun known k =>
        known.set! nodes[k]! (some (opening.extract (BAVC.tau * BAVC.hashLen + 16 * k)
          (BAVC.tau * BAVC.hashLen + 16 * k + 16))))
      (Array.replicate BAVC.numNodes none)
    let t ← (List.range (BAVC.numLeaves - 1)).foldlM (deriveStepIC iv) placed
    let L ← leavesOfIC iv (t.map (·.getD BAVC.zeroBlock)) (fun i => some (BAVC.deltaIndex delta i))
      (fun i => opening.extract (BAVC.hashLen * i) (BAVC.hashLen * i + BAVC.hashLen))
    pure (some L)

theorem evalWithAnswerFn_reconstructIC (g : Table) (E : CTable) (iv opening delta : ByteArray) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) (reconstructIC iv opening delta) =
      @BAVC.reconstruct (icPrg E.cipher) iv opening delta := by
  unfold reconstructIC BAVC.reconstruct
  dsimp only
  split_ifs
  · rfl
  · simp only [evalWithAnswerFn_bind, evalWithAnswerFn_foldlM, evalWithAnswerFn_deriveStepIC,
      evalWithAnswerFn_leavesOfIC, evalWithAnswerFn_pure]


/-! ## The cipher-only parts: their queries -/

section PieceBounds

variable (p : DomIC → Prop) [DecidablePred p] {cc : ℕ}
  (hcq : ∀ k z, IsQueryBoundP (cipherQ k z) p cc)
include hcq

theorem isQueryBoundP_prgIC (key iv : ByteArray) (t c : UInt32) (n : ℕ) :
    IsQueryBoundP (prgIC key iv t c n) p (n * cc) := by
  unfold prgIC
  split
  · have := isQueryBoundP_foldlM p (c := cc) (h := fun out j =>
      (fun y => out ++ ba y) <$> cipherQ (blk 16 key) (blk 16 (AES.ctrBlock iv (c + j.toUInt32) t)))
      (fun b a => by rw [IsQueryBoundP, isQueryBound_map_iff]; exact hcq _ _) (List.range n)
      ByteArray.empty
    simpa using this
  · exact isQueryBoundP_pure p _ _

theorem isQueryBoundP_deriveStepIC (iv : ByteArray) (known : Array (Option ByteArray)) (n : ℕ) :
    IsQueryBoundP (deriveStepIC iv known n) p (2 * cc) := by
  unfold deriveStepIC
  split
  · exact (isQueryBoundP_bind (isQueryBoundP_prgIC p hcq _ _ _ _ 2) fun _ _ =>
      isQueryBoundP_pure p _ 0).mono (by omega)
  · exact isQueryBoundP_pure p _ _

theorem isQueryBoundP_leavesOfIC (iv : ByteArray) (t : Array ByteArray)
    (hidden : Nat → Option Nat) (hiddenCom : Nat → ByteArray) :
    IsQueryBoundP (leavesOfIC iv t hidden hiddenCom) p (BAVC.tau * (2 ^ 8 * (2 * cc))) := by
  unfold leavesOfIC
  dsimp only
  refine (isQueryBoundP_bind (m := 0) (isQueryBoundP_forIn_range p (c := 2 ^ 8 * (2 * cc))
    (fun i r => ?_) _ _) fun _ _ => isQueryBoundP_pure p _ 0).mono (by simp)
  refine (isQueryBoundP_bind (m := 0) (isQueryBoundP_forIn_range p (c := 2 * cc)
    (fun j r' => ?_) _ _) fun _ _ => isQueryBoundP_pure p _ 0).mono ?_
  · split
    · exact isQueryBoundP_pure p _ _
    · exact (isQueryBoundP_bind (isQueryBoundP_prgIC p hcq _ _ _ _ 2) fun _ _ =>
        isQueryBoundP_pure p _ 0).mono (by omega)
  · have hk : 2 ^ BAVC.kOf i ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num)
      (by unfold BAVC.kOf; split <;> omega)
    simpa using Nat.mul_le_mul_right _ hk

end PieceBounds

/-! ## The VOLE expansion -/

/-- `prgOuts` with the cipher as queries. -/
def prgOutsIC (p : Params) (iv : ByteArray) (i dI : ℕ) (key : ℕ → ByteArray) :
    OracleComp specIC (Array (Array UInt64)) :=
  (Array.range (2 ^ BAVC.kOf i)).mapM fun j =>
    if j == dI then pure (zeroCol p)
    else wordsOf <$> prgIC (key j) iv (((1 : UInt32) <<< 31) + i.toUInt32) 0 p.voleColBlocks

/-- `treeColumns` with the cipher as queries. -/
def treeColumnsIC (p : Params) (iv : ByteArray) (i dI : ℕ) (corr : ByteArray)
    (key : ℕ → ByteArray) : OracleComp specIC (Array (Array UInt64)) := do
  let prgOut ← prgOutsIC p iv i dI key
  pure ((Array.range (BAVC.kOf i)).map fun b =>
    (List.range (2 ^ BAVC.kOf i)).foldl
      (fun acc j => if j != dI && (j ^^^ dI).testBit b then xorWords acc prgOut[j]! else acc)
      (if dI.testBit b then corrWords p i corr else zeroCol p))

/-- `convertToVoleAt` with the cipher as queries. -/
def convertToVoleAtIC (p : Params) (dbit : ℕ → Bool) (corr : ℕ → ByteArray) (iv : ByteArray)
    (key : ℕ → ℕ → ByteArray) : OracleComp specIC (Array (Array UInt64)) := do
  let trees ← (Array.range BAVC.tau).mapM fun i =>
    treeColumnsIC p iv i (BAVC.hiddenIndex dbit i) (corr i) (key i)
  pure ((Array.range 128).map fun c =>
    if c < 120 then (trees[BAVC.treeOf c]!)[c - BAVC.bitOffset (BAVC.treeOf c)]! else zeroCol p)

/-- **`convertToVole` with the cipher as queries.** -/
def convertToVoleIC (pf : Proof) (iv : ByteArray) (leaves : BAVC.Leaves) :
    OracleComp specIC (Array (Array UInt64)) :=
  convertToVoleAtIC pf.params (BAVC.deltaBit pf.delta) pf.correctionOf iv (leafKey leaves)

theorem evalWithAnswerFn_prgOutsIC (g : Table) (E : CTable) (p : Params) (iv : ByteArray)
    (i dI : ℕ) (key : ℕ → ByteArray) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) (prgOutsIC p iv i dI key) =
      @prgOuts (icPrg E.cipher) p iv i dI key := by
  unfold prgOutsIC prgOuts
  rw [evalWithAnswerFn_arrayMapM]
  congr 1
  funext j
  split
  · simp [*]
  · simp only [*, evalWithAnswerFn_map, evalWithAnswerFn_prgIC, prgWords]; rfl

theorem evalWithAnswerFn_convertToVoleIC (g : Table) (E : CTable) (pf : Proof) (iv : ByteArray)
    (leaves : BAVC.Leaves) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) (convertToVoleIC pf iv leaves) =
      @convertToVole (icPrg E.cipher) pf iv leaves := by
  unfold convertToVoleIC convertToVoleAtIC convertToVole convertToVoleAt
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_arrayMapM, evalWithAnswerFn_pure]
  unfold treeColumnsIC treeColumns
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_prgOutsIC, evalWithAnswerFn_pure]

section PieceBounds2

variable (p : DomIC → Prop) [DecidablePred p] {cc : ℕ}
  (hcq : ∀ k z, IsQueryBoundP (cipherQ k z) p cc)
include hcq

theorem isQueryBoundP_reconstructIC (iv opening delta : ByteArray) :
    IsQueryBoundP (reconstructIC iv opening delta) p
      ((BAVC.numLeaves - 1) * (2 * cc) + BAVC.tau * (2 ^ 8 * (2 * cc))) := by
  unfold reconstructIC
  dsimp only
  split_ifs
  · exact isQueryBoundP_pure p _ _
  · have hL : (List.range (BAVC.numLeaves - 1)).length = BAVC.numLeaves - 1 := List.length_range
    generalize List.range (BAVC.numLeaves - 1) = L at hL ⊢
    rw [← hL]
    exact isQueryBoundP_bind (isQueryBoundP_foldlM p (isQueryBoundP_deriveStepIC p hcq iv) L _)
      fun t _ => (isQueryBoundP_bind (m := 0) (isQueryBoundP_leavesOfIC p hcq _ _ _ _) fun _ _ =>
        isQueryBoundP_pure p _ 0).mono (Nat.le_of_eq (Nat.add_zero _))

theorem isQueryBoundP_convertToVoleIC (pf : Proof) (iv : ByteArray) (leaves : BAVC.Leaves) :
    IsQueryBoundP (convertToVoleIC pf iv leaves) p
      (BAVC.tau * (2 ^ 8 * (pf.params.voleColBlocks * cc))) := by
  unfold convertToVoleIC convertToVoleAtIC
  refine (isQueryBoundP_bind (n := BAVC.tau * (2 ^ 8 * (pf.params.voleColBlocks * cc))) (m := 0) ?_
    fun _ _ => isQueryBoundP_pure p _ 0).mono (by simp)
  have := isQueryBoundP_arrayMapM p (c := 2 ^ 8 * (pf.params.voleColBlocks * cc))
    (h := fun i => treeColumnsIC pf.params iv i (BAVC.hiddenIndex (BAVC.deltaBit pf.delta) i)
      (pf.correctionOf i) (leafKey leaves i)) (fun i => ?_) (Array.range BAVC.tau)
  · simpa using this
  unfold treeColumnsIC prgOutsIC
  refine (isQueryBoundP_bind (n := 2 ^ 8 * (pf.params.voleColBlocks * cc)) (m := 0) ?_
    fun _ _ => isQueryBoundP_pure p _ 0).mono (by simp)
  refine (isQueryBoundP_arrayMapM p (c := pf.params.voleColBlocks * cc) (fun j => ?_) _).mono ?_
  · split
    · exact isQueryBoundP_pure p _ _
    · rw [IsQueryBoundP, isQueryBound_map_iff]; exact isQueryBoundP_prgIC p hcq _ _ _ _ _
  · have hk : 2 ^ BAVC.kOf i ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num)
      (by unfold BAVC.kOf; split <;> omega)
    simpa using Nat.mul_le_mul_right _ hk

end PieceBounds2

theorem cipherQ_left (k z : Blk) : IsQueryBoundP (cipherQ k z) (fun t => t.isLeft = true) 0 := by
  unfold cipherQ
  rw [← bind_pure (liftM (specIC.query (Sum.inr (k, z))) : OracleComp specIC Blk)]
  exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inl (by simp), fun _ => isQueryBoundP_pure _ _ _⟩

theorem cipherQ_right (k z : Blk) : IsQueryBoundP (cipherQ k z) (fun t => t.isRight = true) 1 := by
  unfold cipherQ
  rw [← bind_pure (liftM (specIC.query (Sum.inr (k, z))) : OracleComp specIC Blk)]
  exact (isQueryBoundP_query_bind_iff _ _ _ _).2 ⟨Or.inr (by norm_num), fun _ => isQueryBoundP_pure _ _ _⟩

/-! ## The verifier -/

/-- A hash computation, run against the hashes and the cipher. -/
def liftH {α : Type} (oa : OracleComp spec α) : OracleComp specIC α :=
  simulateQ (fun d => (liftM (specIC.query (.inl d)) : OracleComp specIC (Ans d))) oa

theorem evalWithAnswerFn_liftH {α : Type} (g : Table) (E : CTable) (oa : OracleComp spec α) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) (liftH oa) =
      evalWithAnswerFn (QueryImpl.ofFn g) oa := by
  rw [liftH, evalWithAnswerFn_simulateQ]
  rfl

/-- The part of `verifyQ` after the BAVC reconstruction, with the VOLE columns `cols` given. -/
def verifyTail (T : CrtTables) (st : Statement) (pf : Proof) (mu1 iv : ByteArray)
    (leaves : BAVC.Leaves) (cols : Array (Array UInt64)) : OracleComp spec Transcript := do
  let lh ← (BAVC.leafHashInputs leaves.coms).mapM (hashQ .h1)
  let com ← hashQ .h1 (BAVC.comInput lh)
  let c1 ← hashQ .h21 (chal1Input pf mu1 com st.binder1)
  let gh ← (gateInputs st.params T iv cols).mapM (hashQ .h5)
  let crt := crtReconstructWith (gateWords gh) st.params (BAVC.deltaBit pf.delta) pf.cmult T cols
  let deltaL := crt.deltaLifted.toGF
  let hV := voleHashReceiver st.params c1 crt.rows crt.qMask deltaL pf.voleCheck
  let muD ← muDelayedQ st c1
  let c2 ← hashQ .h22 (chal2Input pf c1 hV muD st.binder2)
  if deltaL == 0 then return { iv, chal1 := c1, chal2 := c2, error := "Delta = 0" }
  let lb ← combBytesQ st c2
  let check := qsCheck pf c2 (constraintKeys st.params (correctedKeys pf crt.rows deltaL) deltaL
    (st.values c1 lb)) crt.qMask deltaL
  let c3 ← hashQ .h23 (chal3Input pf c2 check)
  return { iv, chal1 := c1, chal2 := c2, qsCheck := gfToBytes check, chal3 := c3,
           accept := c3 == pf.delta }

/-- **The executable verifier with the cipher as queries.** -/
def verifyIC (T : CrtTables) (st : Statement) (proof : ByteArray) :
    OracleComp specIC Transcript := do
  let pf : Proof := { params := st.params, bytes := proof }
  if !pf.checkFormat then return { error := "check_format" }
  let mu1 ← liftH (mu1Q st)
  let iv ← liftH (hashQ .h4 ((pf.ivPre ++ mu1).push 4))
  match ← reconstructIC iv pf.opening pf.delta with
  | none => return { error := "opening" }
  | some leaves =>
    let cols ← convertToVoleIC pf iv leaves
    liftH (verifyTail T st pf mu1 iv leaves cols)

/-- **Against the tables, `verifyIC` is the executable verifier** with the ideal-cipher PRG. -/
theorem evalWithAnswerFn_verifyIC (g : Table) (E : CTable) (T : CrtTables) (st : Statement)
    (proof : ByteArray) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) (verifyIC T st proof) =
      @verify (icPrg E.cipher) (Hashes.ofTable g) T st proof := by
  rw [← @evalWithAnswerFn_verifyQ (icPrg E.cipher) g T st proof]
  unfold verifyIC verifyQ
  dsimp only
  split
  · rfl
  · simp only [evalWithAnswerFn_bind, evalWithAnswerFn_liftH, evalWithAnswerFn_reconstructIC]
    generalize @BAVC.reconstruct (icPrg E.cipher) _ _ _ = R
    cases R with
    | none => rfl
    | some leaves =>
      simp only [evalWithAnswerFn_bind, evalWithAnswerFn_convertToVoleIC, evalWithAnswerFn_liftH,
        verifyTail]

/-! ## The verifier's queries -/

section VerifierBounds

variable {α : Type}

theorem liftH_query_bind (d : Dom) (k : Ans d → OracleComp spec α) :
    liftH (liftM (spec.query d) >>= k) =
      (liftM (specIC.query (.inl d)) : OracleComp specIC (specIC.Range (.inl d))) >>= fun u =>
        liftH (k u) := by
  rw [liftH, simulateQ_bind, simulateQ_spec_query]
  rfl

theorem isKindQueryBoundIC_liftH {oa : OracleComp spec α} {q : Kind → ℕ}
    (h : IsKindQueryBound oa q) : IsKindQueryBoundIC (liftH oa) q := by
  induction oa using OracleComp.inductionOn generalizing q with
  | pure a => trivial
  | query_bind d k ih =>
    rw [isKindQueryBound_query_bind_iff] at h
    rw [liftH_query_bind, IsKindQueryBoundIC, isQueryBound_query_bind_iff]
    exact ⟨h.1, fun u => ih u (h.2 u)⟩

theorem isQueryBoundP_liftH_left {oa : OracleComp spec α} {n : ℕ}
    (h : IsTotalQueryBound oa n) : IsQueryBoundP (liftH oa) (fun t => t.isLeft = true) n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind d k ih =>
    rw [IsTotalQueryBound, isQueryBound_query_bind_iff] at h
    rw [liftH_query_bind, isQueryBoundP_query_bind_iff]
    exact ⟨Or.inr h.1, fun u => by simpa using ih u (h.2 u)⟩

theorem isQueryBoundP_liftH_right (oa : OracleComp spec α) :
    IsQueryBoundP (liftH oa) (fun t => t.isRight = true) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind d k ih =>
    rw [liftH_query_bind, isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp), fun u => by simpa using ih u⟩

/-- A computation without hash queries has any per-kind bound. -/
theorem isKindQueryBoundIC_of_left_zero {oa : OracleComp specIC α}
    (h : IsQueryBoundP oa (fun t => t.isLeft = true) 0) (q : Kind → ℕ) :
    IsKindQueryBoundIC oa q := by
  induction oa using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    rw [IsKindQueryBoundIC, isQueryBound_query_bind_iff]
    cases t with
    | inl d => simp at h
    | inr x => exact ⟨trivial, fun u => ih u (by simpa using h.2 u)⟩

/-- **The tail's queries per kind**: within `verifierQueries`. -/
theorem isKindQueryBound_verifyTail (T : CrtTables) (st : Statement) (pf : Proof)
    (mu1 iv : ByteArray) (leaves : BAVC.Leaves) (cols : Array (Array UInt64)) :
    IsKindQueryBound (verifyTail T st pf mu1 iv leaves cols) verifierQueries := by
  unfold verifyTail
  refine isKindQueryBound_mapM_hashQ_bind _ _
    (by simp [verifierQueries, length_leafHashInputs]) fun lh => ?_
  refine isKindQueryBound_hashQ_bind_iff.2 ⟨by
    simp [verifierQueries, length_leafHashInputs], fun com => ?_⟩
  refine isKindQueryBound_hashQ_bind_iff.2 ⟨by simp [verifierQueries], fun c1 => ?_⟩
  refine isKindQueryBound_mapM_hashQ_bind _ _
    (by simp [verifierQueries, length_gateInputs]) fun gh => ?_
  refine isKindQueryBound_muDelayedQ_bind _ _ (by simp [verifierQueries]) fun muD => ?_
  refine isKindQueryBound_hashQ_bind_iff.2 ⟨by simp [verifierQueries], fun c2 => ?_⟩
  split
  · trivial
  refine isKindQueryBound_combBytesQ_bind _ _
    (fun M => by simp [verifierQueries]) (fun M lb => ?_) (fun lb => ?_)
  all_goals
    refine isKindQueryBound_hashQ_bind_iff.2 ⟨by simp [verifierQueries], fun c3 => trivial⟩

/-- **The tail's queries**: at most `verifierTotal`. -/
theorem isTotalQueryBound_verifyTail (T : CrtTables) (st : Statement) (pf : Proof)
    (mu1 iv : ByteArray) (leaves : BAVC.Leaves) (cols : Array (Array UInt64)) :
    IsTotalQueryBound (verifyTail T st pf mu1 iv leaves cols) verifierTotal := by
  unfold verifyTail verifierTotal
  refine isTotalQueryBound_mapM_hashQ_bind _ _ (by simp [length_leafHashInputs]) fun lh => ?_
  simp only [length_leafHashInputs]
  refine isTotalQueryBound_hashQ_bind_iff.2 ⟨by decide, fun com => ?_⟩
  refine isTotalQueryBound_hashQ_bind_iff.2 ⟨by decide, fun c1 => ?_⟩
  refine isTotalQueryBound_mapM_hashQ_bind _ _ (by simp [length_gateInputs]) fun gh => ?_
  simp only [length_gateInputs]
  refine isTotalQueryBound_muDelayedQ_bind _ _ (by decide) fun muD => ?_
  refine isTotalQueryBound_hashQ_bind_iff.2 ⟨by decide, fun c2 => ?_⟩
  split
  · trivial
  refine isTotalQueryBound_combBytesQ_bind _ _ (by decide) fun lb => ?_
  exact isTotalQueryBound_hashQ_bind_iff.2 ⟨by decide, fun c3 => trivial⟩

end VerifierBounds

/-! ## `verifyIC` satisfies `VerifierIC` -/

/-- `mu₁` and `iv`: the two queries `verifyIC` makes before the reconstruction. -/
def prefQ : Kind → ℕ := fun k => if k = .mu ∨ k = .muDelayed ∨ k = .h4 then 1 else 0

/-- **`verifyIC`'s queries per kind**: `verifierQueries`, and `mu₁` and `iv` once more each. -/
def verifierQueriesIC : Kind → ℕ := prefQ + (prefQ + verifierQueries)

/-- **`verifyIC`'s cipher queries** for a statement with parameters `p`: the GGM derivation (two
blocks per inner node), the leaf commitments (two blocks per leaf, `2⁸` leaves per vector at
most) and the VOLE expansion (`voleColBlocks` blocks per leaf). -/
def cipherCount (p : Params) : ℕ :=
  (BAVC.numLeaves - 1) * (2 * 1) + BAVC.tau * (2 ^ 8 * (2 * 1)) +
    BAVC.tau * (2 ^ 8 * (p.voleColBlocks * 1))

theorem isKindQueryBound_hashQ {k : Kind} {x : ByteArray} {q : Kind → ℕ} (h : 0 < q k) :
    IsKindQueryBound (hashQ k x) q := by
  rw [← bind_pure (hashQ k x)]
  exact isKindQueryBound_hashQ_bind_iff.2 ⟨h, fun _ => trivial⟩

theorem isTotalQueryBound_hashQ {k : Kind} {x : ByteArray} : IsTotalQueryBound (hashQ k x) 1 := by
  rw [← bind_pure (hashQ k x)]
  exact isTotalQueryBound_hashQ_bind_iff.2 ⟨Nat.one_pos, fun _ => trivial⟩

theorem isKindQueryBound_mu1Q (st : Statement) : IsKindQueryBound (mu1Q st) prefQ := by
  unfold mu1Q
  split <;> exact isKindQueryBound_hashQ (by simp [prefQ])

theorem isTotalQueryBound_mu1Q (st : Statement) : IsTotalQueryBound (mu1Q st) 1 := by
  unfold mu1Q
  split <;> exact isTotalQueryBound_hashQ

theorem isKindQueryBoundIC_verifyIC (T : CrtTables) (st : Statement) (proof : ByteArray) :
    IsKindQueryBoundIC (verifyIC T st proof) verifierQueriesIC := by
  unfold verifyIC verifierQueriesIC
  dsimp only
  split
  · trivial
  refine isKindQueryBoundIC_bind (isKindQueryBoundIC_liftH (isKindQueryBound_mu1Q st))
    fun mu1 => ?_
  refine isKindQueryBoundIC_bind (isKindQueryBoundIC_liftH (q := prefQ)
    (isKindQueryBound_hashQ (by simp [prefQ]))) fun iv => ?_
  refine (isKindQueryBoundIC_bind (q₁ := 0) (q₂ := verifierQueries) (isKindQueryBoundIC_of_left_zero
    ((isQueryBoundP_reconstructIC _ cipherQ_left _ _ _).mono (by simp)) 0) fun r => ?_).mono
    (by intro k; simp)
  cases r with
  | none => exact isQueryBound_pure _ _ _ _
  | some leaves =>
    refine (isKindQueryBoundIC_bind (q₁ := 0) (q₂ := verifierQueries) (isKindQueryBoundIC_of_left_zero
      ((isQueryBoundP_convertToVoleIC _ cipherQ_left _ _ _).mono (by simp)) 0) fun cols =>
        isKindQueryBoundIC_liftH (isKindQueryBound_verifyTail T st _ _ _ _ _)).mono
      (by intro k; simp)

theorem isQueryBoundP_left_verifyIC (T : CrtTables) (st : Statement) (proof : ByteArray) :
    IsQueryBoundP (verifyIC T st proof) (fun t => t.isLeft = true) (verifierTotal + 2) := by
  unfold verifyIC
  dsimp only
  split
  · exact isQueryBoundP_pure _ _ _
  refine (isQueryBoundP_bind (n := 1) (m := verifierTotal + 1)
    (isQueryBoundP_liftH_left (isTotalQueryBound_mu1Q st)) fun mu1 _ => ?_).mono (by omega)
  refine (isQueryBoundP_bind (n := 1) (m := verifierTotal)
    (isQueryBoundP_liftH_left isTotalQueryBound_hashQ) fun iv _ => ?_).mono (by omega)
  refine (isQueryBoundP_bind (n := 0) (m := verifierTotal)
    ((isQueryBoundP_reconstructIC _ cipherQ_left _ _ _).mono (by simp)) fun r _ => ?_).mono
    (by omega)
  cases r with
  | none => exact isQueryBoundP_pure _ _ _
  | some leaves =>
    exact (isQueryBoundP_bind (n := 0) (m := verifierTotal)
      ((isQueryBoundP_convertToVoleIC _ cipherQ_left _ _ _).mono (by simp)) fun cols _ =>
        isQueryBoundP_liftH_left (isTotalQueryBound_verifyTail T st _ _ _ _ _)).mono (by omega)

theorem isQueryBoundP_right_verifyIC (T : CrtTables) (st : Statement) (proof : ByteArray) :
    IsQueryBoundP (verifyIC T st proof) (fun t => t.isRight = true) (cipherCount st.params) := by
  unfold verifyIC
  dsimp only
  split
  · exact isQueryBoundP_pure _ _ _
  refine (isQueryBoundP_bind (n := 0) (m := cipherCount st.params) (isQueryBoundP_liftH_right _)
    fun mu1 _ => ?_).mono (by omega)
  refine (isQueryBoundP_bind (n := 0) (m := cipherCount st.params) (isQueryBoundP_liftH_right _)
    fun iv _ => ?_).mono (by omega)
  refine (isQueryBoundP_bind (m := BAVC.tau * (2 ^ 8 * (st.params.voleColBlocks * 1)) + 0)
    (isQueryBoundP_reconstructIC _ cipherQ_right _ _ _) fun r _ => ?_).mono
    (by unfold cipherCount; omega)
  cases r with
  | none => exact isQueryBoundP_pure _ _ _
  | some leaves =>
    exact isQueryBoundP_bind (isQueryBoundP_convertToVoleIC _ cipherQ_right _ _ _) fun cols _ =>
      isQueryBoundP_liftH_right _

/-- **`verifyIC` is a cipher-querying implementation of the executable verifier**: the hypothesis
`VerifierIC` of the protocol games holds, with `verifierQueriesIC` per kind, `verifierTotal + 2`
hash queries and `cipherCount` cipher queries. -/
theorem verifierIC_verifyIC (T : CrtTables) :
    VerifierIC T (fun st pf => (·.accept) <$> verifyIC T st pf) verifierQueriesIC
      (verifierTotal + 2) cipherCount where
  eval g E st pf := by rw [evalWithAnswerFn_map, evalWithAnswerFn_verifyIC]
  kinds st pf := by
    unfold IsKindQueryBoundIC; rw [isQueryBound_map_iff]; exact isKindQueryBoundIC_verifyIC T st pf
  hashes st pf := by
    rw [IsQueryBoundP, isQueryBound_map_iff]; exact isQueryBoundP_left_verifyIC T st pf
  cipher st pf := by
    rw [IsQueryBoundP, isQueryBound_map_iff]; exact isQueryBoundP_right_verifyIC T st pf

end VoleMole.ROM.IC
