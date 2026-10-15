import VoleMole.ROM.UnionBound
import VoleMole.Verifier.Bridge.Accept

/-!
# The executable verifier against the random oracle

The verifier of `Verifier/Verify.lean` is parametrised by its hash functions `Hs : Hashes`, one
per L0 domain (`Verifier/Hashes.lean`). Here it is run against the random oracle of
`ROM/Basic.lean`:

* `Hashes.ofTable g`: the hashes read from a complete answer table `g` (each domain's answer is
  `Kind.outLen` bytes, as SHAKE's);
* `verifyQ T st proof : OracleComp spec Transcript`: the same verifier, with every hash a query to
  the oracle, in the order the verifier makes them (`mu₁`, `iv`, the 17 leaf hashes and `com`,
  `chal1`, the 312 gate hashes, PomFRIT's `mu`, `chal2`, the combination, `chal3`);
* `evalWithAnswerFn_verifyQ`: against a complete table `g`, `verifyQ` returns
  `verify (Hashes.ofTable g) T st proof`, the executable verifier itself;
* `mem_log_verifyQ`: if it accepts, its `H₂¹`, `H₂²`, `H₂³` queries at the verifier's inputs
  (`chal1Input`, `chal2Input`, `chal3Input`) are in its query log;
* `isKindQueryBound_verifyQ`, `isTotalQueryBound_verifyQ`: it makes at most one query to each of
  `H₂¹`, `H₂²`, `H₂³` and `337` in total.

`game T st oa` runs a prover `oa` (outputting a proof and the extractor's data, `ROM/Accept.lean`)
and then `verifyQ` on its proof; its query bounds are the prover's plus the verifier's
(`isKindQueryBound_game`, `isTotalQueryBound_game`).
-/

open ENNReal

namespace VoleMole.ROM

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge OracleComp OracleSpec

/-! ## The hashes of an answer table -/

/-- **The verifier's hashes read from an answer table**: `H_k(x) = g(k, x)`, as bytes. -/
def Hashes.ofTable (g : Table) : Hashes := ⟨fun k x => (g (k, x)).ba⟩

@[simp] lemma Hashes.ofTable_hash (g : Table) (k : Kind) (x : ByteArray) :
    (Hashes.ofTable g).hash k x = (g (k, x)).ba := rfl

/-- One hash query, answered as bytes. -/
def hashQ (k : Kind) (x : ByteArray) : OracleComp spec ByteArray :=
  (fun u : Ans (k, x) => u.ba) <$> (liftM (spec.query (k, x)) : OracleComp spec (Ans (k, x)))

@[simp] lemma evalWithAnswerFn_hashQ (g : Table) (k : Kind) (x : ByteArray) :
    evalWithAnswerFn (QueryImpl.ofFn g) (hashQ k x) = (Hashes.ofTable g).hash k x := rfl

@[simp] lemma evalWithAnswerFn_mapM_hashQ (g : Table) (k : Kind) (l : List ByteArray) :
    evalWithAnswerFn (QueryImpl.ofFn g) (l.mapM (hashQ k)) = l.map ((Hashes.ofTable g).hash k) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.mapM_cons, ih]

/-! ## The verifier as an oracle computation -/

/-- `mu₁` (`Statement.mu1`) as a query. -/
def mu1Q (st : Statement) : OracleComp spec ByteArray :=
  if st.delayed then hashQ .muDelayed (st.dst.push 12)
  else hashQ .mu ((st.instEnc ByteArray.empty ++ st.dst).push 8)

/-- PomFRIT's `mu` in `chal2`'s input (`Statement.muDelayed`) as a query. -/
def muDelayedQ (st : Statement) (c1 : ByteArray) : OracleComp spec ByteArray :=
  if st.delayed then hashQ .mu ((st.instEnc c1 ++ st.dst).push 8) else pure ByteArray.empty

/-- The combination bytes (`Statement.combBytes`) as a query. -/
def combBytesQ (st : Statement) (c2 : ByteArray) : OracleComp spec ByteArray :=
  match st.comb with
  | none => pure ByteArray.empty
  | some (M, dst) => hashQ (.comb M) (c2 ++ dst)

@[simp] lemma evalWithAnswerFn_mu1Q (g : Table) (st : Statement) :
    evalWithAnswerFn (QueryImpl.ofFn g) (mu1Q st) = st.mu1 (Hashes.ofTable g) := by
  unfold mu1Q Statement.mu1 mu; split <;> rfl

@[simp] lemma evalWithAnswerFn_muDelayedQ (g : Table) (st : Statement) (c1 : ByteArray) :
    evalWithAnswerFn (QueryImpl.ofFn g) (muDelayedQ st c1) = st.muDelayed (Hashes.ofTable g) c1 := by
  unfold muDelayedQ Statement.muDelayed mu; split <;> rfl

@[simp] lemma evalWithAnswerFn_combBytesQ (g : Table) (st : Statement) (c2 : ByteArray) :
    evalWithAnswerFn (QueryImpl.ofFn g) (combBytesQ st c2) = st.combBytes (Hashes.ofTable g) c2 := by
  unfold combBytesQ Statement.combBytes
  cases st.comb <;> rfl

/-- **The verifier with every hash a random-oracle query** (`verify`, query by query). -/
def verifyQ (T : CrtTables) (st : Statement) (proof : ByteArray) : OracleComp spec Transcript := do
  let pf : Proof := { params := st.params, bytes := proof }
  if !pf.checkFormat then return { error := "check_format" }
  let mu1 ← mu1Q st
  let iv ← hashQ .h4 ((pf.ivPre ++ mu1).push 4)
  match BAVC.reconstruct iv pf.opening pf.delta with
  | none => return { error := "opening" }
  | some leaves =>
    let lh ← (BAVC.leafHashInputs leaves.coms).mapM (hashQ .h1)
    let com ← hashQ .h1 (BAVC.comInput lh)
    let c1 ← hashQ .h21 (chal1Input pf mu1 com st.binder1)
    let cols := convertToVole pf iv leaves
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

/-- **Against a complete answer table, `verifyQ` is the executable verifier** with the table's
hashes. -/
theorem evalWithAnswerFn_verifyQ (g : Table) (T : CrtTables) (st : Statement)
    (proof : ByteArray) :
    evalWithAnswerFn (QueryImpl.ofFn g) (verifyQ T st proof) =
      verify (Hashes.ofTable g) T st proof := by
  unfold verifyQ verify
  simp only [Id.run]
  by_cases hf : ({ params := st.params, bytes := proof } : Proof).checkFormat = true
  · simp only [hf, Bool.not_true, Bool.false_eq_true, ite_false, evalWithAnswerFn_bind,
      evalWithAnswerFn_mu1Q, evalWithAnswerFn_hashQ, ivOf]
    generalize BAVC.reconstruct _ _ _ = R
    cases R with
    | none => rfl
    | some leaves =>
      simp only [evalWithAnswerFn_bind, evalWithAnswerFn_mapM_hashQ, evalWithAnswerFn_hashQ,
        evalWithAnswerFn_muDelayedQ, apply_ite (evalWithAnswerFn (QueryImpl.ofFn g)),
        evalWithAnswerFn_pure, evalWithAnswerFn_combBytesQ, chal1, chal2, chal3,
        crtReconstruct, crtReconstructAt, gateHashes, BAVC.check]
      show ite _ _ _ = (ite _ _ _ : Transcript)
      split <;> rename_i h <;> simp only [h, ite_true, ite_false, Bool.false_eq_true] <;> rfl
  · simp [hf]; rfl

/-! ## The verifier's run and its queries -/

/-- **The chain of the verifier's run** on `proof` with hashes `Hs`, opening leaves `leaves` and
the extractor's leaf keys `keys`: the proof, `iv`, `H₅`, and the verifier's `chal1`, `h_V`, check
value, `chal2` and constraint evaluator (everything up to the `H₂³` input). -/
def runChain (Hs : Hashes) (T : CrtTables) (st : Statement) (proof : ByteArray)
    (leaves : BAVC.Leaves) (keys : ℕ → ℕ → ByteArray) : Chain :=
  let pf : Proof := { params := st.params, bytes := proof }
  let iv := ivOf Hs pf (st.mu1 Hs)
  let c1 := chal1 Hs pf (st.mu1 Hs) (BAVC.check (Hs.hash .h1) leaves.coms) st.binder1
  let crt := crtReconstruct Hs pf T iv (convertToVole pf iv leaves)
  let deltaL := crt.deltaLifted.toGF
  let hV := voleHashReceiver st.params c1 crt.rows crt.qMask deltaL pf.voleCheck
  let c2 := chal2 Hs pf c1 hV (st.muDelayed Hs c1) st.binder2
  { proof, keys, iv, h5 := Hs.hash .h5, chal1 := c1, hV,
    z := qsCheck pf c2 (constraintKeys st.params (correctedKeys pf crt.rows deltaL) deltaL
      (st.values c1 (st.combBytes Hs c2))) crt.qMask deltaL
    chal2 := c2, vals := st.values c1 (st.combBytes Hs c2) }

/-- The verifier's `H₂¹` input. -/
def runX (Hs : Hashes) (st : Statement) (proof : ByteArray) (leaves : BAVC.Leaves) : ByteArray :=
  chal1Input { params := st.params, bytes := proof } (st.mu1 Hs)
    (BAVC.check (Hs.hash .h1) leaves.coms) st.binder1

/-- The verifier's `H₂²` input, from the chain of its run. -/
def runY (Hs : Hashes) (st : Statement) (ch : Chain) : ByteArray :=
  chal2Input (ch.pf st) ch.chal1 ch.hV (st.muDelayed Hs ch.chal1) st.binder2

/-- The verifier's `H₂³` input, from the chain of its run. -/
def runZ (st : Statement) (ch : Chain) : ByteArray := chal3Input (ch.pf st) ch.chal2 ch.z

/-- The query `t` is in the log of `oa` against the table `g`. -/
def InLog {α : Type} (oa : OracleComp spec α) (g : Table) (t : Dom) : Prop :=
  t ∈ (tableQueryLog oa g).map Sigma.fst

lemma tableQueryLog_hashQ (g : Table) (k : Kind) (x : ByteArray) :
    tableQueryLog (hashQ k x) g = [⟨(k, x), g (k, x)⟩] := by
  rw [hashQ, map_eq_bind_pure_comp, tableQueryLog_bind]
  simp

/-- **On an accepted proof, the verifier's `H₂¹`, `H₂²` and `H₂³` queries are in its log**, at
the inputs of its run. -/
theorem inLog_verifyQ (g : Table) (T : CrtTables) (st : Statement) (proof : ByteArray)
    (h : (verify (Hashes.ofTable g) T st proof).accept = true) {leaves : BAVC.Leaves}
    (hr : BAVC.reconstruct (ivOf (Hashes.ofTable g) ⟨st.params, proof⟩
      (st.mu1 (Hashes.ofTable g))) (Proof.opening ⟨st.params, proof⟩)
      (Proof.delta ⟨st.params, proof⟩) = some leaves) (keys : ℕ → ℕ → ByteArray) :
    let ch := runChain (Hashes.ofTable g) T st proof leaves keys
    InLog (verifyQ T st proof) g (.h21, runX (Hashes.ofTable g) st proof leaves) ∧
      InLog (verifyQ T st proof) g (.h22, runY (Hashes.ofTable g) st ch) ∧
      InLog (verifyQ T st proof) g (.h23, runZ st ch) := by
  obtain ⟨hf, leaves', hr', h0, -⟩ := (accept_iff _ T st proof).1 h
  rw [hr] at hr'
  cases hr'
  simp only [ivOf, crtReconstruct, crtReconstructAt, gateHashes] at hr h0
  unfold InLog verifyQ runX runY runZ runChain
  simp only [hf, Bool.not_true, Bool.false_eq_true, ite_false, tableQueryLog_bind,
    evalWithAnswerFn_mu1Q, tableQueryLog_hashQ, evalWithAnswerFn_hashQ, hr,
    evalWithAnswerFn_mapM_hashQ, evalWithAnswerFn_muDelayedQ, evalWithAnswerFn_combBytesQ,
    List.map_append, List.map_cons, List.mem_append, List.mem_cons, beq_iff_eq, h0, chal1, chal2,
    crtReconstruct, crtReconstructAt, gateHashes, BAVC.check, ivOf, Chain.pf, true_or,
    or_true, and_true]

/-! ## Query bounds -/

lemma hashQ_bind {α : Type} (k : Kind) (x : ByteArray) (f : ByteArray → OracleComp spec α) :
    hashQ k x >>= f = liftM (spec.query (k, x)) >>= fun u : Ans (k, x) => f u.ba := by
  simp [hashQ]

lemma isKindQueryBound_hashQ_bind_iff {α : Type} {k : Kind} {x : ByteArray}
    {f : ByteArray → OracleComp spec α} {q : Kind → ℕ} :
    IsKindQueryBound (hashQ k x >>= f) q ↔
      0 < q k ∧ ∀ u : Ans (k, x), IsKindQueryBound (f u.ba) (Function.update q k (q k - 1)) := by
  rw [hashQ_bind]; exact isKindQueryBound_query_bind_iff

lemma isTotalQueryBound_hashQ_bind_iff {α : Type} {k : Kind} {x : ByteArray}
    {f : ByteArray → OracleComp spec α} {n : ℕ} :
    IsTotalQueryBound (hashQ k x >>= f) n ↔
      0 < n ∧ ∀ u : Ans (k, x), IsTotalQueryBound (f u.ba) (n - 1) := by
  rw [hashQ_bind]; exact isTotalQueryBound_query_bind_iff

/-- `l.length` queries to `k`, then `f`. -/
lemma isKindQueryBound_mapM_hashQ_bind {α : Type} (k : Kind) (l : List ByteArray)
    {f : List ByteArray → OracleComp spec α} {q : Kind → ℕ} (hl : l.length ≤ q k)
    (hf : ∀ ans, IsKindQueryBound (f ans) (Function.update q k (q k - l.length))) :
    IsKindQueryBound (l.mapM (hashQ k) >>= f) q := by
  induction l generalizing q f with
  | nil => simpa using hf []
  | cons x l ih =>
    simp only [List.mapM_cons, bind_assoc, pure_bind]
    refine isKindQueryBound_hashQ_bind_iff.2 ⟨by simp at hl; omega, fun u => ?_⟩
    refine ih (by simp at hl ⊢; omega) fun ans => ?_
    have := hf (u.ba :: ans)
    simp only [List.length_cons, Function.update_self, Function.update_idem] at this ⊢
    rwa [show q k - 1 - l.length = q k - (l.length + 1) by omega]

/-- `l.length` queries, then `f`. -/
lemma isTotalQueryBound_mapM_hashQ_bind {α : Type} (k : Kind) (l : List ByteArray)
    {f : List ByteArray → OracleComp spec α} {n : ℕ} (hl : l.length ≤ n)
    (hf : ∀ ans, IsTotalQueryBound (f ans) (n - l.length)) :
    IsTotalQueryBound (l.mapM (hashQ k) >>= f) n := by
  induction l generalizing n f with
  | nil => simpa using hf []
  | cons x l ih =>
    simp only [List.mapM_cons, bind_assoc, pure_bind]
    refine isTotalQueryBound_hashQ_bind_iff.2 ⟨by simp at hl; omega, fun u => ?_⟩
    refine ih (by simp at hl ⊢; omega) fun ans => ?_
    have := hf (u.ba :: ans)
    simp only [List.length_cons] at this
    rwa [show n - 1 - l.length = n - (l.length + 1) by omega]

lemma IsKindQueryBound.mono {α : Type} {oa : OracleComp spec α} {q q' : Kind → ℕ}
    (h : IsKindQueryBound oa q) (hle : q ≤ q') : IsKindQueryBound oa q' := by
  induction oa using OracleComp.inductionOn generalizing q q' with
  | pure _ => trivial
  | query_bind t k ih =>
    rw [isKindQueryBound_query_bind_iff] at h ⊢
    refine ⟨lt_of_lt_of_le h.1 (hle t.1), fun u => ih u (h.2 u) fun k' => ?_⟩
    by_cases hk : k' = t.1
    · have := hle t.1
      rw [hk, Function.update_self, Function.update_self]
      exact Nat.sub_le_sub_right this 1
    · simp only [Function.update_of_ne hk]; exact hle k'

lemma isKindQueryBound_muDelayedQ_bind {α : Type} (st : Statement) (c1 : ByteArray)
    {f : ByteArray → OracleComp spec α} {q : Kind → ℕ} (h : 0 < q .mu)
    (hf : ∀ u, IsKindQueryBound (f u) (Function.update q .mu (q .mu - 1))) :
    IsKindQueryBound (muDelayedQ st c1 >>= f) q := by
  unfold muDelayedQ
  split
  · exact isKindQueryBound_hashQ_bind_iff.2 ⟨h, fun u => hf _⟩
  · rw [pure_bind]
    refine (hf _).mono fun k => ?_
    by_cases hk : k = .mu
    · subst hk; simp
    · simp [Function.update_of_ne hk]

lemma isKindQueryBound_combBytesQ_bind {α : Type} (st : Statement) (c2 : ByteArray)
    {f : ByteArray → OracleComp spec α} {q : Kind → ℕ} (h : ∀ M, 0 < q (.comb M))
    (hf : ∀ M u, IsKindQueryBound (f u) (Function.update q (.comb M) (q (.comb M) - 1)))
    (hf0 : ∀ u, IsKindQueryBound (f u) q) :
    IsKindQueryBound (combBytesQ st c2 >>= f) q := by
  unfold combBytesQ
  split
  · rw [pure_bind]; exact hf0 _
  · exact isKindQueryBound_hashQ_bind_iff.2 ⟨h _, fun u => hf _ _⟩

lemma length_leafHashInputs (coms : ByteArray) : (BAVC.leafHashInputs coms).length = 17 := by
  simp [BAVC.leafHashInputs, BAVC.tau]

lemma length_gateInputs (p : Params) (T : CrtTables) (iv : ByteArray)
    (cols : Array (Array UInt64)) : (gateInputs p T iv cols).length = 312 := by
  simp [gateInputs, Params.nMult]

/-- The verifier's queries per domain: 18 to `H₁`, 312 to `H₅`, one each to `H₄`, `H₂¹`, `H₂²`,
`H₂³`, `mu₁` (`H₂⁰` or `H₂⁴`), PomFRIT's second `H₂⁰`, and the combination. -/
def verifierQueries : Kind → ℕ
  | .h1 => 18
  | .mu => 2
  | .muDelayed => 1
  | .h3 => 0
  | .h4 => 1
  | .h5 => 312
  | .h21 => 1
  | .h22 => 1
  | .h23 => 1
  | .comb _ => 1

/-- The verifier's total number of queries (at most). -/
def verifierTotal : ℕ := 337

/-- **The verifier's queries per domain** (`verifierQueries`). -/
theorem isKindQueryBound_verifyQ (T : CrtTables) (st : Statement) (proof : ByteArray) :
    IsKindQueryBound (verifyQ T st proof) verifierQueries := by
  unfold verifyQ
  dsimp only
  split
  · trivial
  have hmu : ∀ {f : ByteArray → OracleComp spec Transcript} {q : Kind → ℕ}, 0 < q .mu →
      0 < q .muDelayed → (∀ u, IsKindQueryBound (f u) (Function.update q .mu (q .mu - 1))) →
      (∀ u, IsKindQueryBound (f u) (Function.update q .muDelayed (q .muDelayed - 1))) →
      IsKindQueryBound (mu1Q st >>= f) q := by
    intro f q h1 h2 hf1 hf2
    unfold mu1Q
    split
    · exact isKindQueryBound_hashQ_bind_iff.2 ⟨h2, fun u => hf2 _⟩
    · exact isKindQueryBound_hashQ_bind_iff.2 ⟨h1, fun u => hf1 _⟩
  refine hmu (by decide) (by decide) (fun mu1 => ?_) (fun mu1 => ?_)
  all_goals
    refine isKindQueryBound_hashQ_bind_iff.2 ⟨by simp [verifierQueries], fun iv => ?_⟩
    split
    · trivial
    refine isKindQueryBound_mapM_hashQ_bind _ _
      (by simp [verifierQueries, length_leafHashInputs]) fun lh => ?_
    refine isKindQueryBound_hashQ_bind_iff.2 ⟨by
      simp [verifierQueries, length_leafHashInputs], fun com => ?_⟩
    refine isKindQueryBound_hashQ_bind_iff.2 ⟨by simp [verifierQueries],
      fun c1 => ?_⟩
    refine isKindQueryBound_mapM_hashQ_bind _ _
      (by simp [verifierQueries, length_gateInputs]) fun gh => ?_
    refine isKindQueryBound_muDelayedQ_bind _ _ (by simp [verifierQueries])
      fun muD => ?_
    refine isKindQueryBound_hashQ_bind_iff.2 ⟨by simp [verifierQueries],
      fun c2 => ?_⟩
    split
    · trivial
    refine isKindQueryBound_combBytesQ_bind _ _
      (fun M => by simp [verifierQueries]) (fun M lb => ?_) (fun lb => ?_)
    all_goals
      refine isKindQueryBound_hashQ_bind_iff.2 ⟨by simp [verifierQueries],
        fun c3 => trivial⟩

lemma isTotalQueryBound_muDelayedQ_bind {α : Type} (st : Statement) (c1 : ByteArray)
    {f : ByteArray → OracleComp spec α} {n : ℕ} (h : 0 < n)
    (hf : ∀ u, IsTotalQueryBound (f u) (n - 1)) : IsTotalQueryBound (muDelayedQ st c1 >>= f) n := by
  unfold muDelayedQ
  split
  · exact isTotalQueryBound_hashQ_bind_iff.2 ⟨h, fun u => hf _⟩
  · rw [pure_bind]; exact (hf _).mono (by omega)

lemma isTotalQueryBound_combBytesQ_bind {α : Type} (st : Statement) (c2 : ByteArray)
    {f : ByteArray → OracleComp spec α} {n : ℕ} (h : 0 < n)
    (hf : ∀ u, IsTotalQueryBound (f u) (n - 1)) : IsTotalQueryBound (combBytesQ st c2 >>= f) n := by
  unfold combBytesQ
  split
  · rw [pure_bind]; exact (hf _).mono (by omega)
  · exact isTotalQueryBound_hashQ_bind_iff.2 ⟨h, fun u => hf _⟩

/-- **The verifier makes at most 337 queries.** -/
theorem isTotalQueryBound_verifyQ (T : CrtTables) (st : Statement) (proof : ByteArray) :
    IsTotalQueryBound (verifyQ T st proof) verifierTotal := by
  unfold verifyQ verifierTotal
  dsimp only
  split
  · trivial
  have hmu : ∀ {f : ByteArray → OracleComp spec Transcript} {n : ℕ}, 0 < n →
      (∀ u, IsTotalQueryBound (f u) (n - 1)) → IsTotalQueryBound (mu1Q st >>= f) n := by
    intro f n h hf
    unfold mu1Q
    split <;> exact isTotalQueryBound_hashQ_bind_iff.2 ⟨h, fun u => hf _⟩
  refine hmu (by decide) fun mu1 => ?_
  refine isTotalQueryBound_hashQ_bind_iff.2 ⟨by decide, fun iv => ?_⟩
  split
  · trivial
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

/-! ## The soundness game -/

/-- The extractor's data accompanying a proof: the committed leaf keys it recovered (from the
prover's cipher queries, L1), the trees it treats as known (no dead leaf, L2), and any auxiliary
output `aux` (e.g. the prover's query or cipher log, for the failure events to read). -/
structure ExtData (β : Type) where
  keys : ℕ → ℕ → ByteArray
  known : Finset (Fin BAVC.tau)
  aux : β

variable {β : Type}

/-- **The soundness game**: the prover `oa` outputs a proof (with the extractor's data), then the
verifier checks it against the same random oracle. -/
def game (T : CrtTables) (st : Statement) (oa : OracleComp spec (ByteArray × ExtData β)) :
    OracleComp spec (ByteArray × ExtData β × Transcript) := do
  let r ← oa
  (fun t => (r.1, r.2, t)) <$> verifyQ T st r.1

/-- Against a complete table, the game's output is the prover's, and the executable verifier's
transcript on its proof. -/
theorem evalWithAnswerFn_game (g : Table) (T : CrtTables) (st : Statement)
    (oa : OracleComp spec (ByteArray × ExtData β)) :
    evalWithAnswerFn (QueryImpl.ofFn g) (game T st oa) =
      ((evalWithAnswerFn (QueryImpl.ofFn g) oa).1, (evalWithAnswerFn (QueryImpl.ofFn g) oa).2,
        verify (Hashes.ofTable g) T st (evalWithAnswerFn (QueryImpl.ofFn g) oa).1) := by
  simp [game, evalWithAnswerFn_verifyQ]

/-- The verifier's queries are in the game's log. -/
theorem inLog_game {g : Table} {T : CrtTables} {st : Statement}
    {oa : OracleComp spec (ByteArray × ExtData β)} {t : Dom}
    (h : InLog (verifyQ T st (evalWithAnswerFn (QueryImpl.ofFn g) oa).1) g t) :
    InLog (game T st oa) g t := by
  unfold InLog at h ⊢
  rw [game, tableQueryLog_bind, map_eq_bind_pure_comp, tableQueryLog_bind]
  simp only [List.map_append, List.mem_append]
  exact Or.inr (Or.inl h)

/-- Per-domain query bounds add up along a bind. -/
theorem isKindQueryBound_bind {α β : Type} {oa : OracleComp spec α}
    {ob : α → OracleComp spec β} {q₁ q₂ : Kind → ℕ} (h₁ : IsKindQueryBound oa q₁)
    (h₂ : ∀ a, IsKindQueryBound (ob a) q₂) : IsKindQueryBound (oa >>= ob) (q₁ + q₂) := by
  refine isQueryBound_bind (combine := (· + ·)) (fun t b₁ b₂ b hb => ?_) (fun t b₁ b₂ b hb => ?_)
    h₁ h₂
  · simp only [Pi.add_apply]; omega
  · constructor <;> funext k <;> by_cases hk : k = t.1 <;>
      simp [hk, Function.update_of_ne, Pi.add_apply] <;> omega

/-- **The game's queries per domain**: the prover's and the verifier's. -/
theorem isKindQueryBound_game (T : CrtTables) (st : Statement)
    {oa : OracleComp spec (ByteArray × ExtData β)} {q : Kind → ℕ} (hq : IsKindQueryBound oa q) :
    IsKindQueryBound (game T st oa) (q + verifierQueries) :=
  isKindQueryBound_bind hq fun r =>
    (isQueryBound_map_iff _ _ _ _ _).2 (isKindQueryBound_verifyQ T st r.1)

/-- **The game's total queries**: the prover's and the verifier's 337. -/
theorem isTotalQueryBound_game (T : CrtTables) (st : Statement)
    {oa : OracleComp spec (ByteArray × ExtData β)} {n : ℕ} (hn : IsTotalQueryBound oa n) :
    IsTotalQueryBound (game T st oa) (n + verifierTotal) :=
  isTotalQueryBound_bind hn fun r =>
    (isQueryBound_map_iff _ _ _ _ _).2 (isTotalQueryBound_verifyQ T st r.1)

end VoleMole.ROM
