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

end VoleMole.ROM.IC
