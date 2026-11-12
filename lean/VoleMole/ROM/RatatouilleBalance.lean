import VoleMole.ROM.VerifierIC
import VoleMole.ROM.SpecSound

/-!
# Ratatouille balance as a game (`lean/docs/security/ratatouille.md` §4, Theorem 1)

The balance game BAL (N1): an adversary makes `N` adaptive calls to the honest Issuer of the
executable spec (`Spec/Ratatouille.lean`: `issueResponse`, and `issuerSpend`, which is
`spend_response` with the nullifier store as `ratatouille.hpp` prescribes), choosing the requests,
the contexts and the refunds. The Issuer verifies with the executable Lean verifier against the
hash oracles and the ideal cipher, and signs `Tag(c, x)` with a signer `σ : Target → Option
Preimage` (pqov's `derive_preimage` for its secret key). The adversary wins if for some context
the credits accepted as spent exceed the credits issued plus the refunds granted.

Honest Clients need no separate treatment here: an adversary that runs the honest Client's code
is an adversary of this game, and balance does not distinguish whose requests they are.

## The bound

`balance_le`, `balance_le_lean`: `Pr[win] ≤ N·ε_iss + N·ε_spend + Adv^{uf-tag}(B) + Adv^{coll}(C)`,
where
* `ε_iss`, `ε_spend` are the single-proof extraction bounds of `ROM/SpecSound.lean`
  (`ratatouilleIssue_accept_le_adaptive_spec`, `ratatouilleSpend_accept_le_adaptive_spec`) at
  the query budget of `N` rounds: one per request, applied to the `j`-th prover
  (`ROM/ExtractReduce.lean`, `proverAt`), which runs the game up to round `j` and outputs the
  `j`-th request;
* `B` is an explicit forger of the UF-Tag game (`ufTagAdv`): it outputs the first accepted spend
  whose extracted parent `(Com(nf, ctx, t, r), x)` received no signature before;
* `C` is an explicit `Com` collision finder (`comCollAdv`): two extracted openings with one
  commitment and different `(nf, ctx, t)`.

The proof is per table: on a table where no request fails extraction, `B` does not win and `C`
does not win, every accepted spend satisfies the hypotheses of the deterministic balance theorem
`Spec.Ratatouille.issuer_balance` (`World.Hyp`: the extracted witness is in `R_spend`, and the
state it spends was released earlier with the same opening and refund), so the adversary does not
win; `prEvent_bind_le_sum_of_table` turns this into the bound.

## The Issuer's verifications inside the extraction provers

The `j`-th prover must re-run the Issuer's verifications as queries to the cipher, so that the
straight-line extractor sees them (as the paper's extractor reads the Issuer's queries). The
executable verifier reads the cipher as a table (`icPrg E.cipher`), so `balance_le` takes a
cipher-querying implementation of it (`VerifierIC`); `balance_le_lean` uses `verifyIC`
(`ROM/VerifierIC.lean`), for which `VerifierIC` is a theorem. The game itself verifies with the
executable verifier.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC.RatBalance

open VoleMole.Prob VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ROM VoleMole.ROM.IC
open VoleMole.Spec.Ratatouille VoleMole.EndToEnd VoleMole.ZK.Sim

/-- A byte vector as a byte array. -/
abbrev bOf {n : ℕ} (v : Spec.Ratatouille.Bytes n) : ByteArray := VoleMole.Privacy.Ratatouille.bOf v

/-! ## Statements, the verifier per table, the Issuer -/

/-- The verifier's issuance statement of a spec instance. -/
def issStmt (lr : Bool) (x : IssueInstance) : Statement :=
  ratatouilleIssue (bOf x.c) x.tInit.toNat (bOf x.ctx) lr

/-- The verifier's spend statement of a spec instance, for the Issuer's key `pkU`. -/
def spStmt (lr : Bool) (pkU : UovPk) (x : SpendInstance) : Statement :=
  ratatouilleSpend pkU (bOf x.nf) x.d.toNat (bOf x.cNext) (bOf x.ctx) lr

/-- **The executable verifier at the tables** `g` (hashes) and `E` (cipher). -/
def verT (g : Table) (E : CTable) (st : Statement) (pf : ByteArray) : Bool :=
  (@verify (icPrg E.cipher) (Hashes.ofTable g) CrtGen.tables st pf).accept

/-- The Issuer's signer: `derive_preimage` with its secret key, on a target. -/
abbrev Signer := Target → Option Preimage

variable {Z : Sizes} (lr : Bool) (pkU : UovPk)

/-- **The spec's primitives for the Issuer**: verification by `ver` on the verifier's statements
(the spend statement with the Issuer's own key), signing by the signer. Proving is not used. -/
def romPrim (ver : Statement → ByteArray → Bool) : Prim Z Signer where
  pk := fun _ => pkU.map
  derive := fun σ y => σ y
  proveIssue := fun _ _ _ => none
  verifyIssue := fun x π => ver (issStmt lr x) (bOf π)
  proveSpend := fun _ _ _ => none
  verifySpend := fun x π => ver (spStmt lr pkU x) (bOf π)

/-- The Issuer's responses: to an issuance (`issue_response`), to a spend (`issuerSpend`). -/
abbrev Resp := Except Error (Option Preimage) ⊕ Except Error (Option SpendResult)

/-- **The honest Issuer, one call**, with the spec's functions. -/
def serveP (ver : Statement → ByteArray → Bool) (σ : Signer) (st : IssuerState) :
    Op Z → Resp × IssuerState
  | .issue req tInit ctx => (.inl (issueResponse (romPrim lr pkU ver) σ req tInit ctx), st)
  | .spend req ctx refund =>
    ((.inr (issuerSpend (romPrim lr pkU ver) σ st req ctx refund).2),
      (issuerSpend (romPrim lr pkU ver) σ st req ctx refund).1)

/-- The statement the Issuer verifies for a request. -/
def stmtOf : Op Z → Statement
  | .issue req tInit ctx => issStmt lr ⟨issueReqC req, tInit, ctx⟩
  | .spend req ctx _ => spStmt lr pkU
      ⟨pkU.map, (SpendReq.parse req).nf, (SpendReq.parse req).d, (SpendReq.parse req).cNext, ctx⟩

/-- The proof the Issuer verifies for a request. -/
def proofOf : Op Z → ByteArray
  | .issue req _ _ => bOf (issueReqProof req)
  | .spend req _ _ => bOf (SpendReq.parse req).proof

/-- The Issuer verifies one proof per call: its response depends on `ver` only at the request's
statement and proof. -/
theorem serveP_const (ver : Statement → ByteArray → Bool) (σ : Signer) (st : IssuerState)
    (op : Op Z) :
    serveP lr pkU ver σ st op =
      serveP lr pkU (fun _ _ => ver (stmtOf lr pkU op) (proofOf op)) σ st op := by
  cases op <;> simp [serveP, issueResponse, issuerSpend, spendResponse, romPrim, stmtOf, proofOf]

/-- **The Issuer against a computation verifier** `verQ` (any monad): verify, then respond. -/
def serveM {m : Type → Type} [Monad m] (verQ : Statement → ByteArray → m Bool) (σ : Signer)
    (st : IssuerState) (op : Op Z) : m (Resp × IssuerState) := do
  let b ← verQ (stmtOf lr pkU op) (proofOf op)
  pure (serveP lr pkU (fun _ _ => b) σ st op)

/-- Per table, the computation Issuer is the function Issuer. -/
theorem evalWithAnswerFn_serveM {ι' : Type} {sp : OracleSpec ι'} (f : QueryImpl sp Id)
    (verQ : Statement → ByteArray → OracleComp sp Bool) (ver : Statement → ByteArray → Bool)
    (hv : ∀ st pf, evalWithAnswerFn f (verQ st pf) = ver st pf) (σ : Signer) (st : IssuerState)
    (op : Op Z) :
    evalWithAnswerFn f (serveM lr pkU verQ σ st op) = serveP lr pkU ver σ st op := by
  rw [serveP_const, serveM, evalWithAnswerFn_bind, hv, evalWithAnswerFn_pure]

/-! ## The game -/

variable {S : Type}

/-- The adversary's request at the tables, as a function. -/
def nextT (A : RoundAdv S (Op Z) Resp) (g : Table) (E : CTable) (s : S) : Op Z × S :=
  evalWithAnswerFn (QueryImpl.ofFn (join g E)) (A.next s)

/-- The adversary's request against the hash oracle, with the cipher answered by `E`. -/
def nextS (A : RoundAdv S (Op Z) Resp) (E : CTable) (s : S) : OracleComp spec (Op Z × S) :=
  (·.1) <$> runE E (A.next s)

/-- The game's start: the adversary's initial state, an empty store, an empty transcript. -/
def start (A : RoundAdv S (Op Z) Resp) : S × IssuerState × List (Op Z × Resp) :=
  (A.init, ⟨[]⟩, [])

/-- **The balance game** BAL, `N` rounds, against the hash oracle at the cipher table `E`: the
Issuer verifies with the executable verifier (`verifyQ`, the cipher read from `E`). -/
def balQ (A : RoundAdv S (Op Z) Resp) (N : ℕ) (σ : Signer) (E : CTable) :
    OracleComp spec (S × IssuerState × List (Op Z × Resp)) :=
  roundsM (nextS A E)
    (serveM lr pkU (fun st pf => (·.accept) <$> @verifyQ (icPrg E.cipher) CrtGen.tables st pf) σ)
    A.recv N (start A)

/-- **The game at the tables**, as a function. -/
def balT (A : RoundAdv S (Op Z) Resp) (N : ℕ) (σ : Signer) (g : Table) (E : CTable) :
    S × IssuerState × List (Op Z × Resp) :=
  roundsT (nextT A g E) (serveP lr pkU (verT g E) σ) A.recv N (start A)

theorem evalWithAnswerFn_nextS (A : RoundAdv S (Op Z) Resp) (g : Table) (E : CTable) (s : S) :
    evalWithAnswerFn (QueryImpl.ofFn g) (nextS A E s) = nextT A g E s := by
  rw [nextS, evalWithAnswerFn_map, evalWithAnswerFn_runE]
  rfl

/-- Per table, the game is the function game. -/
theorem evalWithAnswerFn_balQ (A : RoundAdv S (Op Z) Resp) (N : ℕ) (σ : Signer) (g : Table)
    (E : CTable) :
    evalWithAnswerFn (QueryImpl.ofFn g) (balQ lr pkU A N σ E) = balT lr pkU A N σ g E :=
  evalWithAnswerFn_roundsM _ _ _ _ _ _ (evalWithAnswerFn_nextS A g E)
    (evalWithAnswerFn_serveM lr pkU _ _ _ (fun st pf => by
      rw [evalWithAnswerFn_map, @evalWithAnswerFn_verifyQ (icPrg E.cipher)]; rfl) σ) N _

/-! ## Winning: spent beyond issued and refunded, in some context -/

/-- The credits a round issues: `T_init` of an accepted issuance. -/
def issRec : Op Z × Resp → List (Context × ℕ)
  | (.issue _ tInit ctx, .inl (.ok (some _))) => [(ctx, tInit.toNat)]
  | _ => []

/-- The credits a round spends: `d` of an accepted spend. -/
def spRec : Op Z × Resp → List (Context × ℕ)
  | (.spend _ ctx _, .inr (.ok (some out))) => [(ctx, out.d.toNat)]
  | _ => []

/-- The refund a round grants: `x'` of an accepted spend. -/
def rfRec : Op Z × Resp → List (Context × ℕ)
  | (.spend _ ctx refund, .inr (.ok (some _))) => [(ctx, refund.toNat)]
  | _ => []

/-- The credits issued, per context. -/
def issuedOf (tr : List (Op Z × Resp)) : List (Context × ℕ) := tr.flatMap issRec

/-- The credits accepted as spent, per context. -/
def spentOf (tr : List (Op Z × Resp)) : List (Context × ℕ) := tr.flatMap spRec

/-- The refunds granted, per context. -/
def refundedOf (tr : List (Op Z × Resp)) : List (Context × ℕ) := tr.flatMap rfRec

/-- **The adversary wins BAL**: in some context, the credits accepted as spent exceed the
credits issued plus the refunds granted. -/
def Win (tr : List (Op Z × Resp)) : Prop :=
  ∃ c, total c (issuedOf tr) + total c (refundedOf tr) < total c (spentOf tr)


/-! ## Byte conversions -/

theorem bytesVec_bOf {n : ℕ} (v : Spec.Ratatouille.Bytes n) : SpecRel.bytesVec n (bOf v) = v := by
  apply Vector.ext
  intro i hi
  have h1 := SpecRel.fn_bytesVec n (bOf v) hi
  rw [SpecRel.fnOf_eq_getD, show bOf v = toBA v.toList from rfl, SpecRel.toL_toBA,
    VoleMole.Privacy.Ratatouille.getD_toList_fn] at h1
  simpa [Bytes.fn, hi, bOf, VoleMole.Privacy.Ratatouille.bOf] using h1

theorem issueInstOf_bOf (c : Commitment) (tInit : Credits) (ctx : Context) :
    SpecRel.issueInstOf (bOf c) tInit.toNat (bOf ctx) = ⟨c, tInit, ctx⟩ := by
  simp [SpecRel.issueInstOf, bytesVec_bOf]

theorem spendInstOf_bOf (nf : Nullifier) (d : Credits) (cNext : Commitment) (ctx : Context) :
    SpecRel.spendInstOf pkU (bOf nf) d.toNat (bOf cNext) (bOf ctx) = ⟨pkU.map, nf, d, cNext, ctx⟩ := by
  simp [SpecRel.spendInstOf, bytesVec_bOf]

/-! ## The extraction provers: the `j`-th request, re-run against the cipher -/

/-- Issuance statement indices `(c, T_init, ctx)`. -/
abbrev IIdx := Commitment × Credits × Context

/-- Spend statement indices `(nf, d, c', ctx)` (the key is the Issuer's). -/
abbrev SIdx := Nullifier × Credits × Commitment × Context

/-- The byte-array issuance instance of an index (`ROM/SpecSound.lean`'s `inst`). -/
def instI (i : IIdx) : ByteArray × ℕ × ByteArray := (bOf i.1, i.2.1.toNat, bOf i.2.2)

/-- The issuance statement family. -/
def stI (i : IIdx) : Statement := ratatouilleIssue (instI i).1 (instI i).2.1 (instI i).2.2 lr

/-- The spend statement family. -/
def stS (i : SIdx) : Statement :=
  ratatouilleSpend pkU (bOf i.1) i.2.1.toNat (bOf i.2.2.1) (bOf i.2.2.2) lr

/-- `R_iss` at an index, on the decoded witness. -/
def WI (i : IIdx) : ByteArray → (ℕ → Arith.GF128) → Prop := fun _ w =>
  IssueRel (SpecRel.issueInstOf (instI i).1 (instI i).2.1 (instI i).2.2) (SpecRel.issueWitOfR w)

/-- `R_spend` at an index, on the decoded witness. -/
def WS (i : SIdx) : ByteArray → (ℕ → Arith.GF128) → Prop := fun _ w =>
  SpendRel (SpecRel.spendInstOf pkU (bOf i.1) i.2.1.toNat (bOf i.2.2.1) (bOf i.2.2.2))
    (SpecRel.spendWitOf w)

def zI : IIdx := (Vector.replicate 32 0, 0, Vector.replicate 16 0)
def zS : SIdx := (Vector.replicate 24 0, 0, Vector.replicate 32 0, Vector.replicate 16 0)

/-- An issuance request read as a proof and a statement index (a spend: a dummy). -/
def pickI : Op Z → ByteArray × (IIdx × Unit)
  | .issue req tInit ctx => (bOf (issueReqProof req), ((issueReqC req, tInit, ctx), ()))
  | .spend _ _ _ => (ByteArray.empty, (zI, ()))

/-- A spend request read as a proof and a statement index (an issuance: a dummy). -/
def pickS : Op Z → ByteArray × (SIdx × Unit)
  | .spend req ctx _ => (bOf (SpendReq.parse req).proof,
      (((SpendReq.parse req).nf, (SpendReq.parse req).d, (SpendReq.parse req).cNext, ctx), ()))
  | .issue _ _ _ => (ByteArray.empty, (zS, ()))

variable (verQ : Statement → ByteArray → OracleComp specIC Bool)

/-- **The `j`-th issuance prover**: the game up to round `j` with the Issuer verifying by `verQ`,
then the `j`-th request. -/
def provI (A : RoundAdv S (Op Z) Resp) (σ : Signer) (j : ℕ) :
    OracleComp specIC (ByteArray × (IIdx × Unit)) :=
  proverAt A (serveM lr pkU verQ σ) (⟨[]⟩ : IssuerState) pickI j

/-- **The `j`-th spend prover.** -/
def provS (A : RoundAdv S (Op Z) Resp) (σ : Signer) (j : ℕ) :
    OracleComp specIC (ByteArray × (SIdx × Unit)) :=
  proverAt A (serveM lr pkU verQ σ) (⟨[]⟩ : IssuerState) pickS j

/-- The single-proof game of the `j`-th issuance request (`gameA`). -/
def gameI (A : RoundAdv S (Op Z) Resp) (σ : Signer) (j : ℕ) (E : CTable) :
    OracleComp spec (Out ((IIdx × Unit) × QueryLog specIC)) :=
  gameA CrtGen.tables (stI lr) (provI lr pkU verQ A σ j) E

/-- The single-proof game of the `j`-th spend request. -/
def gameS (A : RoundAdv S (Op Z) Resp) (σ : Signer) (j : ℕ) (E : CTable) :
    OracleComp spec (Out ((SIdx × Unit) × QueryLog specIC)) :=
  gameA CrtGen.tables (stS lr pkU) (provS lr pkU verQ A σ j) E

/-- **Extraction fails** in the issuance game (the event of
`ratatouilleIssue_accept_le_adaptive_spec`). -/
def failI (E : CTable) (r : Out ((IIdx × Unit) × QueryLog specIC)) : Prop :=
  r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (stI lr (stOut r)) (WI (stOut r)) r

/-- **Extraction fails** in the spend game (`ratatouilleSpend_accept_le_adaptive_spec`). -/
def failS (E : CTable) (r : Out ((SIdx × Unit) × QueryLog specIC)) : Prop :=
  r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (stS lr pkU (stOut r)) (WS pkU (stOut r)) r

/-- A default issuance witness. -/
def dI : IssueWitness := ⟨Vector.replicate 24 0, Vector.replicate 16 0⟩

/-- A default spend witness. -/
def dS : SpendWitness :=
  ⟨0, Vector.replicate 16 0, 0, Vector.replicate 119 0, Vector.replicate 24 0, 0,
    Vector.replicate 16 0⟩

/-- **The extracted issuance witness** of a game output (a default if extraction fails). -/
noncomputable def annI (E : CTable) (r : Out ((IIdx × Unit) × QueryLog specIC)) : IssueWitness :=
  ((@extWit _ (icPrg E.cipher) (stI lr (stOut r)) (WI (stOut r)) r).map SpecRel.issueWitOfR).getD dI

/-- **The extracted spend witness** of a game output. -/
noncomputable def annS (E : CTable) (r : Out ((SIdx × Unit) × QueryLog specIC)) : SpendWitness :=
  ((@extWit _ (icPrg E.cipher) (stS lr pkU (stOut r)) (WS pkU (stOut r)) r).map
    SpecRel.spendWitOf).getD dS

theorem annI_spec (E : CTable) (r : Out ((IIdx × Unit) × QueryLog specIC))
    (h : @Extracted (icPrg E.cipher) _ (stI lr (stOut r)) (WI (stOut r)) r) :
    IssueRel ⟨(stOut r).1, (stOut r).2.1, (stOut r).2.2⟩ (annI lr E r) := by
  obtain ⟨w, hw, hW⟩ := @extWit_spec _ (icPrg E.cipher) _ _ _ h
  rw [annI, hw]
  have := hW
  simp only [WI, instI, issueInstOf_bOf] at this
  exact this

theorem annS_spec (E : CTable) (r : Out ((SIdx × Unit) × QueryLog specIC))
    (h : @Extracted (icPrg E.cipher) _ (stS lr pkU (stOut r)) (WS pkU (stOut r)) r) :
    SpendRel ⟨pkU.map, (stOut r).1, (stOut r).2.1, (stOut r).2.2.1, (stOut r).2.2.2⟩ (annS lr pkU E r) := by
  obtain ⟨w, hw, hW⟩ := @extWit_spec _ (icPrg E.cipher) _ _ _ h
  rw [annS, hw]
  have := hW
  simp only [WS, spendInstOf_bOf] at this
  exact this

/-! ## The events of the reduction -/

/-- The pairs `(c, x)` a round released a signature on: `(c, 0)` for an accepted issuance,
`(c', x')` for an accepted spend. -/
def relRec : Op Z × Resp → List (Commitment × Credits)
  | (.issue req _ _, .inl (.ok (some _))) => [(issueReqC req, 0)]
  | (.spend req _ refund, .inr (.ok (some _))) => [((SpendReq.parse req).cNext, refund)]
  | _ => []

/-- An opening `(nf, ctx, t, r)` of `Com`. -/
abbrev Opening4 := Nullifier × Context × Credits × Opening

/-- The commitment of an opening. -/
def comOf (o : Opening4) : Commitment := com o.1 o.2.1 o.2.2.1 o.2.2.2

/-- What a commitment binds: `(nf, ctx, t)`. -/
def triOf (o : Opening4) : Nullifier × Context × Credits := (o.1, o.2.1, o.2.2.1)

/-- The openings a round's extracted witnesses give: an accepted issuance's `(nf, ctx, T_init, r)`;
an accepted spend's parent `(nf, ctx, t, r)` and change `(nf', ctx, t', r')`. -/
def opensRec (wi : IssueWitness) (ws : SpendWitness) : Op Z × Resp → List Opening4
  | (.issue _ tInit ctx, .inl (.ok (some _))) => [(wi.nf, ctx, tInit, wi.r)]
  | (.spend req ctx _, .inr (.ok (some _))) =>
      [((SpendReq.parse req).nf, ctx, ws.t, ws.r), (ws.nf', ctx, ws.t', ws.r')]
  | _ => []

/-- All extracted openings of a run, with the extracted witnesses `wI k`, `wS k` of round `k`. -/
def opens (wI : ℕ → IssueWitness) (wS : ℕ → SpendWitness) (tr : List (Op Z × Resp)) :
    List Opening4 :=
  tr.zipIdx.flatMap fun p => opensRec (wI p.2) (wS p.2) p.1

/-- **A `Com` collision among the extracted openings**: two openings with one commitment and
different `(nf, ctx, t)`. -/
def ComColl (wI : ℕ → IssueWitness) (wS : ℕ → SpendWitness) (tr : List (Op Z × Resp)) : Prop :=
  ∃ o ∈ opens wI wS tr, ∃ o' ∈ opens wI wS tr, comOf o = comOf o' ∧ triOf o ≠ triOf o'

/-- **A forgery**: an accepted spend `j` whose extracted witness carries a valid signature `s`,
`P(s) = Tag(c, x)` for its parent `c = Com(nf, ctx, t, r)`, on a pair `(c, x)` on which no round
before `j` released a signature. -/
def Forge (wS : ℕ → SpendWitness) (tr : List (Op Z × Resp)) : Prop :=
  ∃ j req ctx refund out, tr[j]? = some (.spend req ctx refund, .inr (.ok (some out))) ∧
    uovEval pkU.map (wS j).s = tag (com (SpendReq.parse req).nf ctx (wS j).t (wS j).r) (wS j).x ∧
    (com (SpendReq.parse req).nf ctx (wS j).t (wS j).r, (wS j).x) ∉ (tr.take j).flatMap relRec

/-! ## The deterministic core: no failure, no win -/

section Core

variable (ver : Statement → ByteArray → Bool) (σ : Signer) (nT : S → Op Z × S)
  (recv : S → Resp → S) (s0 : S)

/-- The run's state after `k` rounds. -/
def yT (k : ℕ) : S × IssuerState × List (Op Z × Resp) :=
  roundsT nT (serveP lr pkU ver σ) recv k (s0, ⟨[]⟩, [])

/-- Round `k`'s request and response. -/
def recT (k : ℕ) : Op Z × Resp := recOf nT (serveP lr pkU ver σ) (yT lr pkU ver σ nT recv s0 k)

theorem trace_yT (n : ℕ) :
    (yT lr pkU ver σ nT recv s0 n).2.2 = (List.range n).map (recT lr pkU ver σ nT recv s0) := by
  rw [yT, roundsT_trace]; rfl

theorem getElem?_trace {n k : ℕ} (hk : k < n) :
    (yT lr pkU ver σ nT recv s0 n).2.2[k]? = some (recT lr pkU ver σ nT recv s0 k) := by
  rw [trace_yT, List.getElem?_map, List.getElem?_range hk]; rfl

theorem take_trace {n k : ℕ} (hk : k ≤ n) :
    (yT lr pkU ver σ nT recv s0 n).2.2.take k = (yT lr pkU ver σ nT recv s0 k).2.2 := by
  rw [trace_yT, trace_yT, ← List.map_take, List.take_range, min_eq_left hk]

/-- The store after round `k`. -/
theorem store_succ (k : ℕ) :
    (yT lr pkU ver σ nT recv s0 (k + 1)).2.1 =
      (serveP lr pkU ver σ (yT lr pkU ver σ nT recv s0 k).2.1
        (recT lr pkU ver σ nT recv s0 k).1).2 := rfl

/-- Round `k`'s response is the Issuer's at the store after `k` rounds. -/
theorem resp_eq (k : ℕ) :
    (recT lr pkU ver σ nT recv s0 k).2 =
      (serveP lr pkU ver σ (yT lr pkU ver σ nT recv s0 k).2.1
        (recT lr pkU ver σ nT recv s0 k).1).1 := rfl

/-- The ledger's world run on rounds `0 … n - 1`, annotated with the extracted witnesses. -/
def osT (wI : ℕ → IssueWitness) (wS : ℕ → SpendWitness) (n : ℕ) :
    List (Op Z × IssueWitness × SpendWitness) :=
  (List.range n).map fun k => ((recT lr pkU ver σ nT recv s0 k).1, wI k, wS k)

theorem World.run_append (P : Prim Z Signer) (w : World)
    (l₁ l₂ : List (Op Z × IssueWitness × SpendWitness)) :
    World.run P σ w (l₁ ++ l₂) = World.run P σ (World.run P σ w l₁) l₂ := by
  induction l₁ generalizing w with
  | nil => rfl
  | cons o l ih => exact ih _

/-- The entries a round releases into the ledger. -/
def entRec (wi : IssueWitness) (ws : SpendWitness) : Op Z × Resp → List Entry
  | (.issue _ tInit ctx, .inl (.ok (some _))) => [⟨(ctx, wi.nf), tInit.toNat, 0⟩]
  | (.spend _ ctx refund, .inr (.ok (some _))) => [⟨(ctx, ws.nf'), ws.t'.toNat, refund.toNat⟩]
  | _ => []

theorem total_nil (c : Context) : total c [] = 0 := rfl

theorem total_append (c : Context) (l₁ l₂ : List (Context × ℕ)) :
    total c (l₁ ++ l₂) = total c l₁ + total c l₂ := by
  simp [total, List.filter_append, List.map_append, List.sum_append]

/-- **One round on the ledger.** Run with the extracted witnesses, the ledger world follows the
game: same store, the ledger invariant is kept (given the round's hypothesis `World.Hyp`), the
totals grow by the round's issued, spent and refunded credits, and the released entries by the
round's. -/
theorem step_inv (wI : ℕ → IssueWitness) (wS : ℕ → SpendWitness) (n : ℕ) (w : World)
    (hst : w.st = (yT lr pkU ver σ nT recv s0 n).2.1) (hsk : w.st.store = w.L.spentKeys)
    (hI : w.L.Inv)
    (hH : w.Hyp (romPrim lr pkU ver) σ ((recT lr pkU ver σ nT recv s0 n).1, wI n, wS n)) :
    let w' := World.step (romPrim lr pkU ver) σ w ((recT lr pkU ver σ nT recv s0 n).1, wI n, wS n)
    w'.st = (yT lr pkU ver σ nT recv s0 (n + 1)).2.1 ∧ w'.st.store = w'.L.spentKeys ∧
      w'.L.Inv ∧
      (∀ c, total c w'.L.issued =
        total c w.L.issued + total c (issRec (recT lr pkU ver σ nT recv s0 n))) ∧
      (∀ c, total c w'.L.spent =
        total c w.L.spent + total c (spRec (recT lr pkU ver σ nT recv s0 n))) ∧
      (∀ c, total c w'.L.refunded =
        total c w.L.refunded + total c (rfRec (recT lr pkU ver σ nT recv s0 n))) ∧
      w'.L.released = entRec (wI n) (wS n) (recT lr pkU ver σ nT recv s0 n) ++ w.L.released := by
  obtain ⟨hsk', hI'⟩ := World.step_inv (romPrim lr pkU ver) σ w _ hsk hH hI
  refine ⟨?_, hsk', hI', ?_⟩
  · rw [store_succ, ← hst]
    generalize (recT lr pkU ver σ nT recv s0 n).1 = op
    cases op with
    | issue req tInit ctx =>
      simp only [World.step, serveP]; split <;> rfl
    | spend req ctx refund =>
      simp only [World.step, serveP]; split <;> rename_i h <;> rw [h]
  · have hr := resp_eq lr pkU ver σ nT recv s0 n
    rw [← hst] at hr
    generalize recT lr pkU ver σ nT recv s0 n = rn at hr ⊢
    obtain ⟨op, resp⟩ := rn
    simp only at hr
    subst hr
    cases op with
    | issue req tInit ctx =>
      simp only [World.step, serveP]
      generalize issueResponse (romPrim lr pkU ver) σ req tInit ctx = r
      rcases r with e | _ | s <;>
        simp [Ledger.step, issRec, spRec, rfRec, entRec, total_cons, total_nil, add_comm]
    | spend req ctx refund =>
      simp only [World.step, serveP]
      generalize issuerSpend (romPrim lr pkU ver) σ w.st req ctx refund = q
      obtain ⟨st', r⟩ := q
      rcases r with e | _ | out <;>
        simp [Ledger.step, issRec, spRec, rfRec, entRec, total_cons, total_nil, add_comm]

/-- An accepted spend's response carries the request's nullifier and amount. -/
theorem issuerSpend_out {P : Prim Z Signer} {st : IssuerState} {req : SpendRequest Z}
    {ctx : Context} {refund : Credits} {out : SpendResult}
    (h : (issuerSpend P σ st req ctx refund).2 = .ok (some out)) :
    out.nf = (SpendReq.parse req).nf ∧ out.d = (SpendReq.parse req).d := by
  rcases issuerSpend_store (Prod.mk.eta (p := issuerSpend P σ st req ctx refund)).symm with
    ⟨-, hne⟩ | ⟨out', h₁, hresp, -, -⟩
  · exact absurd h (hne out)
  rw [h] at h₁; cases h₁
  simp only [spendResponse] at hresp
  split_ifs at hresp
  · cases hresp
  · cases hd : P.derive σ (tag (SpendReq.parse req).cNext refund) with
    | none => rw [hd] at hresp; cases hresp
    | some s => rw [hd] at hresp; cases hresp; exact ⟨rfl, rfl⟩

theorem mem_opens {wI : ℕ → IssueWitness} {wS : ℕ → SpendWitness} {tr : List (Op Z × Resp)}
    {k : ℕ} {r : Op Z × Resp} (hk : tr[k]? = some r) {o : Opening4}
    (ho : o ∈ opensRec (wI k) (wS k) r) : o ∈ opens wI wS tr :=
  List.mem_flatMap.2 ⟨(r, k), List.mem_zipIdx_iff_getElem?.2 hk, ho⟩

/-- **The deterministic core of Theorem 1.** On a run where every accepted issuance and spend
has an extracted witness of its relation, no accepted spend's parent is a forgery and the
extracted openings contain no `Com` collision, the adversary does not win: per context, spent
`≤` issued + refunded. (Through the ledger world of `Spec/Ratatouille.lean` and its invariant,
`World.step_inv`.) -/
theorem no_win (wI : ℕ → IssueWitness) (wS : ℕ → SpendWitness) (N : ℕ)
    (hI : ∀ k req tInit ctx s, (yT lr pkU ver σ nT recv s0 N).2.2[k]? =
      some (.issue req tInit ctx, .inl (.ok (some s))) →
        IssueRel ⟨issueReqC req, tInit, ctx⟩ (wI k))
    (hS : ∀ k req ctx refund out, (yT lr pkU ver σ nT recv s0 N).2.2[k]? =
      some (.spend req ctx refund, .inr (.ok (some out))) →
        SpendRel ⟨pkU.map, (SpendReq.parse req).nf, (SpendReq.parse req).d,
          (SpendReq.parse req).cNext, ctx⟩ (wS k))
    (hF : ¬ Forge pkU wS (yT lr pkU ver σ nT recv s0 N).2.2)
    (hC : ¬ ComColl wI wS (yT lr pkU ver σ nT recv s0 N).2.2) :
    ¬ Win (yT lr pkU ver σ nT recv s0 N).2.2 := by
  set tr := (yT lr pkU ver σ nT recv s0 N).2.2 with htr
  let P : Prim Z Signer := romPrim lr pkU ver
  let w0 : World := ⟨⟨[]⟩, Ledger.empty⟩
  -- The invariant after `n` rounds.
  have inv : ∀ n ≤ N,
      let w := World.run P σ w0 (osT lr pkU ver σ nT recv s0 wI wS n)
      w.st = (yT lr pkU ver σ nT recv s0 n).2.1 ∧ w.st.store = w.L.spentKeys ∧ w.L.Inv ∧
        (∀ c, total c w.L.issued = total c (issuedOf (yT lr pkU ver σ nT recv s0 n).2.2) ∧
          total c w.L.spent = total c (spentOf (yT lr pkU ver σ nT recv s0 n).2.2) ∧
          total c w.L.refunded = total c (refundedOf (yT lr pkU ver σ nT recv s0 n).2.2)) ∧
        (∀ k < n, ∀ e ∈ entRec (wI k) (wS k) ((recT lr pkU ver σ nT recv s0) k), e ∈ w.L.released) := by
    intro n
    induction n with
    | zero =>
      intro _
      have h0 : (yT lr pkU ver σ nT recv s0 0).2.2 = [] := rfl
      refine ⟨rfl, rfl, fun c => by simp [osT, World.run, w0, Ledger.empty, total, Ledger.live,
        liveSum], fun c => ?_, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
      rw [h0]
      simp [osT, World.run, w0, Ledger.empty, issuedOf, spentOf, refundedOf, total]
    | succ n ih =>
      intro hn
      obtain ⟨hst, hsk, hInv, htot, hrel⟩ := ih (Nat.le_of_succ_le hn)
      have hnN : n < N := hn
      set w := World.run P σ w0 (osT lr pkU ver σ nT recv s0 wI wS n) with hw
      have hos : osT lr pkU ver σ nT recv s0 wI wS (n + 1) =
          osT lr pkU ver σ nT recv s0 wI wS n ++ [(((recT lr pkU ver σ nT recv s0) n).1, wI n, wS n)] := by
        simp [osT, List.range_succ]
      -- The round's hypothesis.
      have hH : w.Hyp P σ (((recT lr pkU ver σ nT recv s0) n).1, wI n, wS n) := by
        have hr := resp_eq lr pkU ver σ nT recv s0 n
        have htrn : tr[n]? = some ((recT lr pkU ver σ nT recv s0) n) := getElem?_trace lr pkU ver σ nT recv s0 hnN
        generalize hrn : (recT lr pkU ver σ nT recv s0) n = rn at hr htrn ⊢
        obtain ⟨op, resp⟩ := rn
        cases op with
        | issue req tInit ctx => trivial
        | spend req ctx refund =>
          intro out hout
          have hresp : resp = .inr (.ok (some out)) := by
            simp only [serveP] at hr; rw [hr, ← hst]; exact congrArg Sum.inr hout
          subst hresp
          obtain ⟨hnf, hd⟩ := issuerSpend_out σ hout
          have hrel' := hS n req ctx refund out htrn
          refine ⟨by rw [hnf, hd]; exact hrel', ?_⟩
          -- The parent was released before round `n`.
          have hmem : (com (SpendReq.parse req).nf ctx (wS n).t (wS n).r, (wS n).x) ∈
              (tr.take n).flatMap relRec := by
            by_contra hnot
            exact hF ⟨n, req, ctx, refund, out, htrn, hrel'.1, hnot⟩
          rw [htr, take_trace lr pkU ver σ nT recv s0 hnN.le, trace_yT] at hmem
          obtain ⟨rk, hrk, hpk⟩ := List.mem_flatMap.1 hmem
          obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hrk
          have hkn : k < n := List.mem_range.1 hk
          have htrk : tr[k]? = some (recT lr pkU ver σ nT recv s0 k) :=
            getElem?_trace lr pkU ver σ nT recv s0 (hkn.trans hnN)
          have hpar : ((SpendReq.parse req).nf, ctx, (wS n).t, (wS n).r) ∈ opens wI wS tr :=
            mem_opens htrn (by simp [opensRec])
          have hrelk := hrel k hkn
          generalize hrk' : recT lr pkU ver σ nT recv s0 k = rk' at htrk hpk hrelk
          rw [hnf]
          obtain ⟨opk, respk⟩ := rk'
          cases opk with
          | issue req' tInit' ctx' =>
            rcases respk with (_ | _ | s') | _ <;> simp [relRec] at hpk
            obtain ⟨hc, hx⟩ := hpk
            have hik := hI k req' tInit' ctx' s' htrk
            have ho' : ((wI k).nf, ctx', tInit', (wI k).r) ∈ opens wI wS tr :=
              mem_opens htrk (by simp [opensRec])
            by_cases htri : triOf ((SpendReq.parse req).nf, ctx, (wS n).t, (wS n).r) =
                triOf ((wI k).nf, ctx', tInit', (wI k).r)
            · simp only [triOf, Prod.mk.injEq] at htri
              obtain ⟨h1, h2, h3⟩ := htri
              have := hrelk ⟨(ctx', (wI k).nf), tInit'.toNat, 0⟩ (by simp [entRec])
              rw [h1, h2, h3, hx]; simpa using this
            · exact absurd ⟨_, hpar, _, ho', by rw [comOf, comOf, hc]; exact hik, htri⟩ hC
          | spend req' ctx' refund' =>
            rcases respk with _ | (_ | _ | out') <;> simp [relRec] at hpk
            obtain ⟨hc, hx⟩ := hpk
            have hsk' := hS k req' ctx' refund' out' htrk
            have ho' : ((wS k).nf', ctx', (wS k).t', (wS k).r') ∈ opens wI wS tr :=
              mem_opens htrk (by simp [opensRec])
            by_cases htri : triOf ((SpendReq.parse req).nf, ctx, (wS n).t, (wS n).r) =
                triOf ((wS k).nf', ctx', (wS k).t', (wS k).r')
            · simp only [triOf, Prod.mk.injEq] at htri
              obtain ⟨h1, h2, h3⟩ := htri
              have := hrelk ⟨(ctx', (wS k).nf'), (wS k).t'.toNat, refund'.toNat⟩ (by simp [entRec])
              rw [h1, h2, h3, hx]; simpa using this
            · exact absurd ⟨_, hpar, _, ho', by rw [comOf, comOf, hc]; exact hsk'.2.1, htri⟩ hC
      obtain ⟨hst', hsk', hInv', hi', hs', hr', hrl'⟩ :=
        step_inv lr pkU ver σ nT recv s0 wI wS n w hst hsk hInv hH
      rw [hos, World.run_append]
      refine ⟨hst', hsk', hInv', fun c => ?_, fun k hk e he => ?_⟩
      · have htrs : (yT lr pkU ver σ nT recv s0 (n + 1)).2.2 =
            (yT lr pkU ver σ nT recv s0 n).2.2 ++ [(recT lr pkU ver σ nT recv s0) n] := rfl
        rw [htrs]
        obtain ⟨t1, t2, t3⟩ := htot c
        simp only [issuedOf, spentOf, refundedOf] at t1 t2 t3 ⊢
        simp only [List.flatMap_append, List.flatMap_singleton, total_append, World.run]
        rw [← hw]
        exact ⟨by rw [hi' c, t1], by rw [hs' c, t2], by rw [hr' c, t3]⟩
      · simp only [World.run]
        rw [← hw]
        rw [hrl']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
        · exact List.mem_append_right _ (hrel k hk e he)
        · exact List.mem_append_left _ he
  obtain ⟨-, -, hInv, htot, -⟩ := inv N le_rfl
  rintro ⟨c, hc⟩
  have h1 := hInv c
  obtain ⟨t1, t2, t3⟩ := htot c
  rw [← htr] at t1 t2 t3
  rw [t1, t2, t3] at h1
  omega

end Core

/-! ## Acceptance means verification -/

theorem issueResponse_verify {P : Prim Z Signer} {σ : Signer} {req : IssueRequest Z}
    {tInit : Credits} {ctx : Context} {s : Preimage}
    (h : issueResponse P σ req tInit ctx = .ok (some s)) :
    P.verifyIssue ⟨issueReqC req, tInit, ctx⟩ (issueReqProof req) = true := by
  cases hv : P.verifyIssue ⟨issueReqC req, tInit, ctx⟩ (issueReqProof req)
  · exfalso
    revert h
    simp only [issueResponse, hv, Bool.not_false, ite_true]
    split_ifs <;> simp
  · rfl

theorem issuerSpend_verify {P : Prim Z Signer} {σ : Signer} {st : IssuerState}
    {req : SpendRequest Z} {ctx : Context} {refund : Credits} {out : SpendResult}
    (h : (issuerSpend P σ st req ctx refund).2 = .ok (some out)) :
    P.verifySpend ⟨P.pk σ, (SpendReq.parse req).nf, (SpendReq.parse req).d,
      (SpendReq.parse req).cNext, ctx⟩ (SpendReq.parse req).proof = true := by
  rcases issuerSpend_store (Prod.mk.eta (p := issuerSpend P σ st req ctx refund)).symm with
    ⟨-, hne⟩ | ⟨out', h₁, hresp, -, -⟩
  · exact absurd h (hne out)
  simp only [spendResponse] at hresp
  split_ifs at hresp with hv
  · cases hresp
  · simpa using hv

/-! ## Per table: the run, the extraction games, the events -/

section PerTable

variable (A : RoundAdv S (Op Z) Resp) (N : ℕ) (σ : Signer) {qV : Kind → ℕ} {nV : ℕ} {eV : Params → ℕ}

/-- The game's state after `k` rounds at the tables. -/
abbrev yG (g : Table) (E : CTable) (k : ℕ) := yT lr pkU (verT g E) σ (nextT A g E) A.recv A.init k

/-- Round `k` at the tables. -/
abbrev recG (g : Table) (E : CTable) (k : ℕ) :=
  recT lr pkU (verT g E) σ (nextT A g E) A.recv A.init k

theorem provI_eval (hver : VerifierIC CrtGen.tables verQ qV nV eV) (g : Table) (E : CTable)
    (k : ℕ) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) (provI lr pkU verQ A σ k) =
      pickI (recG lr pkU A σ g E k).1 :=
  evalWithAnswerFn_proverAt A _ (QueryImpl.ofFn (join g E)) (nextT A g E) _ (fun _ => rfl)
    (evalWithAnswerFn_serveM lr pkU _ verQ _ (fun st pf => hver.eval g E st pf) σ) _ pickI k

theorem provS_eval (hver : VerifierIC CrtGen.tables verQ qV nV eV) (g : Table) (E : CTable)
    (k : ℕ) :
    evalWithAnswerFn (QueryImpl.ofFn (join g E)) (provS lr pkU verQ A σ k) =
      pickS (recG lr pkU A σ g E k).1 :=
  evalWithAnswerFn_proverAt A _ (QueryImpl.ofFn (join g E)) (nextT A g E) _ (fun _ => rfl)
    (evalWithAnswerFn_serveM lr pkU _ verQ _ (fun st pf => hver.eval g E st pf) σ) _ pickS k

theorem lt_of_getElem? {tr : List (Op Z × Resp)} {k : ℕ} {r : Op Z × Resp} (h : tr[k]? = some r) :
    k < tr.length := by
  by_contra hk; rw [List.getElem?_eq_none (by omega)] at h; cases h

theorem length_trace (g : Table) (E : CTable) : (yG lr pkU A σ g E N).2.2.length = N := by
  rw [trace_yT]; simp

/-- **An accepted issuance whose extraction game does not fail has an extracted witness.** -/
theorem ext_issue (hver : VerifierIC CrtGen.tables verQ qV nV eV) (g : Table) (E : CTable)
    {k : ℕ} {req : IssueRequest Z} {tInit : Credits} {ctx : Context} {s : Preimage}
    (hk : (yG lr pkU A σ g E N).2.2[k]? = some (.issue req tInit ctx, .inl (.ok (some s))))
    (hf : ¬ failI lr E (evalWithAnswerFn (QueryImpl.ofFn g) (gameI lr pkU verQ A σ k E))) :
    IssueRel ⟨issueReqC req, tInit, ctx⟩
      (annI lr E (evalWithAnswerFn (QueryImpl.ofFn g) (gameI lr pkU verQ A σ k E))) := by
  have hkN : k < N := length_trace lr pkU A N σ g E ▸ lt_of_getElem? hk
  rw [getElem?_trace _ _ _ _ _ _ _ hkN, Option.some.injEq] at hk
  have hresp := resp_eq lr pkU (verT g E) σ (nextT A g E) A.recv A.init k
  obtain ⟨h1, h2, h3⟩ := gameA_out CrtGen.tables (stI lr) (provI lr pkU verQ A σ k) E g
  rw [provI_eval lr pkU verQ A σ hver g E k] at h1 h2 h3
  dsimp only [recG] at h1 h2 h3
  rw [hk] at h1 h2 h3 hresp
  simp only [pickI] at h1 h2 h3
  simp only [serveP, Sum.inl.injEq] at hresp
  have hv := issueResponse_verify hresp.symm
  have hacc : (evalWithAnswerFn (QueryImpl.ofFn g) (gameI lr pkU verQ A σ k E)).2.2.accept = true := by
    rw [gameI, h3]; exact hv
  have hext : @Extracted (icPrg E.cipher) _ (stI lr (stOut (evalWithAnswerFn (QueryImpl.ofFn g)
      (gameI lr pkU verQ A σ k E)))) (WI (stOut (evalWithAnswerFn (QueryImpl.ofFn g)
      (gameI lr pkU verQ A σ k E)))) (evalWithAnswerFn (QueryImpl.ofFn g)
      (gameI lr pkU verQ A σ k E)) := by
    by_contra hne; exact hf ⟨hacc, hne⟩
  have := annI_spec lr E _ hext
  rw [gameI, h2] at this
  exact this

/-- **An accepted spend whose extraction game does not fail has an extracted witness.** -/
theorem ext_spend (hver : VerifierIC CrtGen.tables verQ qV nV eV) (g : Table) (E : CTable)
    {k : ℕ} {req : SpendRequest Z} {ctx : Context} {refund : Credits} {out : SpendResult}
    (hk : (yG lr pkU A σ g E N).2.2[k]? = some (.spend req ctx refund, .inr (.ok (some out))))
    (hf : ¬ failS lr pkU E (evalWithAnswerFn (QueryImpl.ofFn g) (gameS lr pkU verQ A σ k E))) :
    SpendRel ⟨pkU.map, (SpendReq.parse req).nf, (SpendReq.parse req).d,
        (SpendReq.parse req).cNext, ctx⟩
      (annS lr pkU E (evalWithAnswerFn (QueryImpl.ofFn g) (gameS lr pkU verQ A σ k E))) := by
  have hkN : k < N := length_trace lr pkU A N σ g E ▸ lt_of_getElem? hk
  rw [getElem?_trace _ _ _ _ _ _ _ hkN, Option.some.injEq] at hk
  have hresp := resp_eq lr pkU (verT g E) σ (nextT A g E) A.recv A.init k
  obtain ⟨h1, h2, h3⟩ := gameA_out CrtGen.tables (stS lr pkU) (provS lr pkU verQ A σ k) E g
  rw [provS_eval lr pkU verQ A σ hver g E k] at h1 h2 h3
  dsimp only [recG] at h1 h2 h3
  rw [hk] at h1 h2 h3 hresp
  simp only [pickS] at h1 h2 h3
  simp only [serveP, Sum.inr.injEq] at hresp
  have hv := issuerSpend_verify hresp.symm
  have hacc : (evalWithAnswerFn (QueryImpl.ofFn g) (gameS lr pkU verQ A σ k E)).2.2.accept = true := by
    rw [gameS, h3]; exact hv
  have hext : @Extracted (icPrg E.cipher) _ (stS lr pkU (stOut (evalWithAnswerFn (QueryImpl.ofFn g)
      (gameS lr pkU verQ A σ k E)))) (WS pkU (stOut (evalWithAnswerFn (QueryImpl.ofFn g)
      (gameS lr pkU verQ A σ k E)))) (evalWithAnswerFn (QueryImpl.ofFn g)
      (gameS lr pkU verQ A σ k E)) := by
    by_contra hne; exact hf ⟨hacc, hne⟩
  have := annS_spec lr pkU E _ hext
  rw [gameS, h2] at this
  exact this

end PerTable

/-! ## The reduction's experiments -/

/-- An output of the issuance extraction game. -/
abbrev OutI := Out ((IIdx × Unit) × QueryLog specIC)

/-- An output of the spend extraction game. -/
abbrev OutS := Out ((SIdx × Unit) × QueryLog specIC)

/-- **The reduction's run**: the game's transcript and, for every round `k < N`, the extraction
games of the `k`-th request (as an issuance and as a spend). Per table its parts are the game and
the single-proof games (`evalWithAnswerFn_master`). -/
def master (A : RoundAdv S (Op Z) Resp) (N : ℕ) (σ : Signer) (E : CTable) :
    OracleComp spec (List (Op Z × Resp) × List OutI × List OutS) := do
  let r ← balQ lr pkU A N σ E
  let rIs ← (List.range N).mapM fun k => gameI lr pkU verQ A σ k E
  let rSs ← (List.range N).mapM fun k => gameS lr pkU verQ A σ k E
  pure (r.2.2, rIs, rSs)

/-- The extracted issuance witness of round `k`, read off the reduction's run. -/
noncomputable def wIof (E : CTable) (m : List (Op Z × Resp) × List OutI × List OutS) (k : ℕ) :
    IssueWitness :=
  (m.2.1[k]?.map (annI lr E)).getD dI

/-- The extracted spend witness of round `k`, read off the reduction's run. -/
noncomputable def wSof (E : CTable) (m : List (Op Z × Resp) × List OutI × List OutS) (k : ℕ) :
    SpendWitness :=
  (m.2.2[k]?.map (annS lr pkU E)).getD dS

/-- **The forger `B` succeeds**: some accepted spend's extracted witness is a valid signature on
a pair `(Com(nf, ctx, t, r), x)` that received no signature before (`Forge`). -/
def ForgeEv (E : CTable) (m : List (Op Z × Resp) × List OutI × List OutS) : Prop :=
  Forge pkU (wSof lr pkU E m) m.1

/-- **The collision finder `C` succeeds**: the extracted openings contain a `Com` collision. -/
def CollEv (E : CTable) (m : List (Op Z × Resp) × List OutI × List OutS) : Prop :=
  ComColl (wIof lr E m) (wSof lr pkU E m) m.1

/-- **`Adv^{uf-tag}`**: the probability that the forger `B` (the reduction's run, outputting the
first accepted spend whose extracted parent is a forgery) succeeds. -/
noncomputable def forgeAdv (A : RoundAdv S (Op Z) Resp) (N : ℕ) (σ : Signer) : ℝ≥0∞ :=
  Pr{let E ← $ᵗ CTable; let m ← (simulateQ randomOracle (master lr pkU verQ A N σ E)).run' ∅}[
    ForgeEv lr pkU E m]

/-- **`Adv^{coll}_{Com}`**: the probability that the collision finder `C` succeeds. -/
noncomputable def collAdv (A : RoundAdv S (Op Z) Resp) (N : ℕ) (σ : Signer) : ℝ≥0∞ :=
  Pr{let E ← $ᵗ CTable; let m ← (simulateQ randomOracle (master lr pkU verQ A N σ E)).run' ∅}[
    CollEv lr pkU E m]

theorem evalWithAnswerFn_master (A : RoundAdv S (Op Z) Resp) (N : ℕ) (σ : Signer) (g : Table)
    (E : CTable) :
    evalWithAnswerFn (QueryImpl.ofFn g) (master lr pkU verQ A N σ E) =
      ((balT lr pkU A N σ g E).2.2,
        (List.range N).map fun k => evalWithAnswerFn (QueryImpl.ofFn g) (gameI lr pkU verQ A σ k E),
        (List.range N).map fun k => evalWithAnswerFn (QueryImpl.ofFn g) (gameS lr pkU verQ A σ k E)) := by
  simp only [master, evalWithAnswerFn_bind, evalWithAnswerFn_mapM, evalWithAnswerFn_pure,
    evalWithAnswerFn_balQ]

/-! ## The single-proof bounds -/

/-- The bound of `ratatouilleIssue_accept_le_adaptive_spec` for `q_E` cipher queries and `q k`
hash queries of kind `k`. -/
noncomputable def epsIss (qE : ℕ) (q : Kind → ℕ) : ℝ≥0∞ :=
  (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 3776) +
    (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
    (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
    (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
    ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
    chainHitEps q + stmtBindEps q

/-- The bound of `ratatouilleSpend_accept_le_adaptive_spec` for `q_E` cipher queries, `n` hash
queries and `q k` hash queries of kind `k`. -/
noncomputable def epsSpend (qE n : ℕ) (q : Kind → ℕ) : ℝ≥0∞ :=
  (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
    (q .h22 + 1) * (ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 12282) +
      (2 ^ 128 : ℝ≥0∞)⁻¹ + ((n + 2 + verifierTotal : ℕ) : ℝ≥0∞) / 2 ^ 448) +
    (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
    (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) +
    (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) +
    ((qE * 2 : ℕ) : ℝ≥0∞) * (((512 * q .h1 : ℕ) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹) +
    chainHitEpsComb q Arith.Ratatouille.uovM + stmtBindEps q

section Bounds

variable (A : RoundAdv S (Op Z) Resp) (N : ℕ) (σ : Signer) {qV : Kind → ℕ} {nV : ℕ} {eV : Params → ℕ}
  (hver : VerifierIC CrtGen.tables verQ qV nV eV) {qA : Kind → ℕ} {nA eA : ℕ}
  (hqA : ∀ s, IsKindQueryBoundIC (A.next s) qA)
  (hnA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isLeft = true) nA)
  (heA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isRight = true) eA)
include hver

theorem serveM_kinds (σ : Signer) (st : IssuerState) (op : Op Z) :
    IsKindQueryBoundIC (serveM lr pkU verQ σ st op) (qV + 0) :=
  isKindQueryBoundIC_bind (hver.kinds _ _) fun _ => isQueryBound_pure _ _ _ _

/-- The cipher budget of one Issuer call: the larger of the issuance and spend verifications'. -/
def eVR (eV : Params → ℕ) : ℕ :=
  max (eV (ratatouilleIssue .empty 0 .empty lr).params)
    (eV (ratatouilleSpend pkU .empty 0 .empty .empty lr).params)

theorem serveM_cipher (σ : Signer) (st : IssuerState) (op : Op Z) :
    IsQueryBoundP (serveM lr pkU verQ σ st op) (fun t => t.isRight = true) (eVR lr pkU eV + 0) := by
  refine isQueryBoundP_bind ((hver.cipher _ _).mono ?_) fun _ _ => isQueryBoundP_pure _ _ 0
  cases op with
  | issue req tInit ctx => exact le_max_left _ _
  | spend req ctx refund => exact le_max_right _ _

omit hver in
theorem serveM_P (p : DomIC → Prop) [DecidablePred p] {v : ℕ}
    (hv : ∀ st pf, IsQueryBoundP (verQ st pf) p v) (σ : Signer) (st : IssuerState) (op : Op Z) :
    IsQueryBoundP (serveM lr pkU verQ σ st op) p (v + 0) :=
  isQueryBoundP_bind (hv _ _) fun _ _ => isQueryBoundP_pure p _ 0

include hqA hnA heA

/-- The `k`-th prover's budget, `k < N`: at most the budget of `N` rounds. -/
theorem prover_bounds {ι β : Type} (pick : Op Z → ByteArray × (ι × β)) {k : ℕ} (hk : k < N) :
    IsKindQueryBoundIC (proverAt A (serveM lr pkU verQ σ) (⟨[]⟩ : IssuerState) pick k)
        (N • (qA + qV)) ∧
      IsQueryBoundP (proverAt A (serveM lr pkU verQ σ) (⟨[]⟩ : IssuerState) pick k)
        (fun t => t.isLeft = true) (N * (nA + nV)) ∧
      IsQueryBoundP (proverAt A (serveM lr pkU verQ σ) (⟨[]⟩ : IssuerState) pick k)
        (fun t => t.isRight = true) (N * (eA + eVR lr pkU eV)) := by
  refine ⟨?_, ?_, ?_⟩
  · refine (isKindQueryBoundIC_proverAt A _ hqA (fun st op => by
      simpa using serveM_kinds lr pkU verQ hver σ st op) _ pick k).mono fun j => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    exact Nat.mul_le_mul_right _ hk
  · exact (isQueryBoundP_proverAt A _ _ hnA (fun st op => by
      simpa using serveM_P lr pkU verQ _ hver.hashes σ st op) _ pick k).mono
      (Nat.mul_le_mul_right _ hk)
  · exact (isQueryBoundP_proverAt A _ _ heA (fun st op => by
      simpa using serveM_cipher lr pkU verQ hver σ st op) _ pick k).mono
      (Nat.mul_le_mul_right _ hk)

/-- **Extraction of the `k`-th issuance request** (`ratatouilleIssue_accept_le_adaptive_spec`
applied to the `k`-th prover). -/
theorem pr_failI_le {k : ℕ} (hk : k < N) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameI lr pkU verQ A σ k E)).run' ∅}[
      failI lr E r] ≤ epsIss (N * (eA + eVR lr pkU eV)) (N • (qA + qV)) := by
  obtain ⟨hq, -, hqE⟩ := prover_bounds lr pkU verQ A N σ hver hqA hnA heA pickI hk
  exact ratatouilleIssue_accept_le_adaptive_spec instI (fun s => UInt64.toNat_lt _) lr
    (SpecRel.hinj_ratatouilleIssue_spec (fun i : IIdx => (⟨i.1, i.2.1, i.2.2⟩ : IssueInstance)) lr
      (fun a b h => by simpa [Prod.ext_iff] using h))
    (provI lr pkU verQ A σ k) _ hqE _ hq

/-- **Extraction of the `k`-th spend request** (`ratatouilleSpend_accept_le_adaptive_spec`). -/
theorem pr_failS_le (hdig : pkU.digest.size = 32) {k : ℕ} (hk : k < N) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameS lr pkU verQ A σ k E)).run' ∅}[
      failS lr pkU E r] ≤ epsSpend (N * (eA + eVR lr pkU eV)) (N * (nA + nV)) (N • (qA + qV)) := by
  obtain ⟨hq, hn, hqE⟩ := prover_bounds lr pkU verQ A N σ hver hqA hnA heA pickS hk
  exact ratatouilleSpend_accept_le_adaptive_spec (fun _ => pkU) (fun i : SIdx => bOf i.1)
    (fun i => i.2.1.toNat) (fun i => UInt64.toNat_lt _) (fun i => bOf i.2.2.1)
    (fun i => bOf i.2.2.2) lr
    (SpecRel.hinj_ratatouilleSpend_spec
      (fun i : SIdx => (⟨pkU.map, i.1, i.2.1, i.2.2.1, i.2.2.2⟩ : SpendInstance)) (fun _ => pkU) lr
      (fun _ => hdig) (fun a b h => by simpa [Prod.ext_iff] using h))
    (provS lr pkU verQ A σ k) _ hqE _ hn _ hq

end Bounds

/-! ## Theorem 1 -/

open Classical in
/-- The reduction's experiments, each returning whether its event happened: the extraction games
of the issuance and spend requests of every round, the forger and the collision finder. -/
noncomputable def exps (A : RoundAdv S (Op Z) Resp) (N : ℕ) (σ : Signer) :
    (ℕ ⊕ ℕ) ⊕ Bool → CTable → OracleComp spec Bool
  | .inl (.inl k), E => (fun r => decide (failI lr E r)) <$> gameI lr pkU verQ A σ k E
  | .inl (.inr k), E => (fun r => decide (failS lr pkU E r)) <$> gameS lr pkU verQ A σ k E
  | .inr true, E => (fun m => decide (ForgeEv lr pkU E m)) <$> master lr pkU verQ A N σ E
  | .inr false, E => (fun m => decide (CollEv lr pkU E m)) <$> master lr pkU verQ A N σ E

/-- The probability that an experiment of the reduction returns `true`. -/
noncomputable def prExp (A : RoundAdv S (Op Z) Resp) (N : ℕ) (σ : Signer)
    (i : (ℕ ⊕ ℕ) ⊕ Bool) : ℝ≥0∞ :=
  Pr{let E ← $ᵗ CTable; let b ← (simulateQ randomOracle (exps lr pkU verQ A N σ i E)).run' ∅}[b = true]

/-- **Per table, a win is an extraction failure, a forgery or a collision.** -/
theorem win_imp (A : RoundAdv S (Op Z) Resp) (N : ℕ) (σ : Signer) {qV : Kind → ℕ} {nV : ℕ} {eV : Params → ℕ}
    (hver : VerifierIC CrtGen.tables verQ qV nV eV) (E : CTable) (g : Table)
    (hw : Win (evalWithAnswerFn (QueryImpl.ofFn g) (balQ lr pkU A N σ E)).2.2) :
    ∃ i ∈ ((Finset.range N).disjSum (Finset.range N)).disjSum (Finset.univ : Finset Bool),
      evalWithAnswerFn (QueryImpl.ofFn g) (exps lr pkU verQ A N σ i E) = true := by
  classical
  by_contra hall
  push Not at hall
  have hI : ∀ k < N, ¬ failI lr E (evalWithAnswerFn (QueryImpl.ofFn g) (gameI lr pkU verQ A σ k E)) :=
    fun k hk => by
      have := hall (.inl (.inl k)) (by simp [hk])
      simpa [exps, evalWithAnswerFn_map] using this
  have hS : ∀ k < N, ¬ failS lr pkU E
      (evalWithAnswerFn (QueryImpl.ofFn g) (gameS lr pkU verQ A σ k E)) :=
    fun k hk => by
      have := hall (.inl (.inr k)) (by simp [hk])
      simpa [exps, evalWithAnswerFn_map] using this
  have hF : ¬ ForgeEv lr pkU E (evalWithAnswerFn (QueryImpl.ofFn g) (master lr pkU verQ A N σ E)) := by
    have := hall (.inr true) (by simp)
    simpa [exps, evalWithAnswerFn_map] using this
  have hC : ¬ CollEv lr pkU E (evalWithAnswerFn (QueryImpl.ofFn g) (master lr pkU verQ A N σ E)) := by
    have := hall (.inr false) (by simp)
    simpa [exps, evalWithAnswerFn_map] using this
  rw [evalWithAnswerFn_master] at hF hC
  rw [evalWithAnswerFn_balQ] at hw
  -- The extracted witnesses of the reduction's run are the single-proof games'.
  have hwI : ∀ k < N, wIof lr E ((balT lr pkU A N σ g E).2.2,
      (List.range N).map fun k => evalWithAnswerFn (QueryImpl.ofFn g) (gameI lr pkU verQ A σ k E),
      (List.range N).map fun k => evalWithAnswerFn (QueryImpl.ofFn g) (gameS lr pkU verQ A σ k E)) k =
      annI lr E (evalWithAnswerFn (QueryImpl.ofFn g) (gameI lr pkU verQ A σ k E)) := fun k hk => by
    simp [wIof, List.getElem?_map, List.getElem?_range hk]
  have hwS : ∀ k < N, wSof lr pkU E ((balT lr pkU A N σ g E).2.2,
      (List.range N).map fun k => evalWithAnswerFn (QueryImpl.ofFn g) (gameI lr pkU verQ A σ k E),
      (List.range N).map fun k => evalWithAnswerFn (QueryImpl.ofFn g) (gameS lr pkU verQ A σ k E)) k =
      annS lr pkU E (evalWithAnswerFn (QueryImpl.ofFn g) (gameS lr pkU verQ A σ k E)) := fun k hk => by
    simp [wSof, List.getElem?_map, List.getElem?_range hk]
  refine no_win lr pkU (verT g E) σ (nextT A g E) A.recv A.init _ _ N ?_ ?_ hF hC hw
  · intro k req tInit ctx s hk
    have hkN : k < N := length_trace lr pkU A N σ g E ▸ lt_of_getElem? hk
    rw [hwI k hkN]
    exact ext_issue lr pkU verQ A N σ hver g E hk (hI k hkN)
  · intro k req ctx refund out hk
    have hkN : k < N := length_trace lr pkU A N σ g E ▸ lt_of_getElem? hk
    rw [hwS k hkN]
    exact ext_spend lr pkU verQ A N σ hver g E hk (hS k hkN)

/-- **Theorem 1 (balance), for the executable Issuer, in the random-oracle and ideal-cipher
model.** For an adversary making `N` calls to the Issuer, with at most `qA k` hash queries of kind
`k`, `nA` hash queries and `eA` cipher queries per call, and a cipher-querying implementation
`verQ` of the executable verifier (`VerifierIC`, with `qV`, `nV`, `eV`; `eVR` the larger cipher
budget of the issuance and spend statements):

    Pr[win BAL] ≤ N·ε_iss + N·ε_spend + Adv^{uf-tag}(B) + Adv^{coll}_{Com}(C),

with `ε_iss`, `ε_spend` the single-proof extraction bounds of `ROM/SpecSound.lean` at the budget
of `N` rounds (`N(eA + eVR)` cipher queries, `N(nA + nV)` hash queries, `N(qA + qV)` per kind),
`B` the forger and `C` the collision finder run by the reduction (`forgeAdv`, `collAdv`). -/
theorem balance_le (A : RoundAdv S (Op Z) Resp) (N : ℕ) (σ : Signer)
    (hdig : pkU.digest.size = 32) {qV : Kind → ℕ} {nV : ℕ} {eV : Params → ℕ}
    (hver : VerifierIC CrtGen.tables verQ qV nV eV) {qA : Kind → ℕ} {nA eA : ℕ}
    (hqA : ∀ s, IsKindQueryBoundIC (A.next s) qA)
    (hnA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isLeft = true) nA)
    (heA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isRight = true) eA) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (balQ lr pkU A N σ E)).run' ∅}[
        Win r.2.2] ≤
      N * epsIss (N * (eA + eVR lr pkU eV)) (N • (qA + qV)) +
        N * epsSpend (N * (eA + eVR lr pkU eV)) (N * (nA + nV)) (N • (qA + qV)) +
        forgeAdv lr pkU verQ A N σ + collAdv lr pkU verQ A N σ := by
  classical
  refine le_trans (prEvent_bind_le_sum_of_table ($ᵗ CTable) (balQ lr pkU A N σ)
    (((Finset.range N).disjSum (Finset.range N)).disjSum Finset.univ)
    (exps lr pkU verQ A N σ) (fun _ r => Win r.2.2)
    (fun E g hw => win_imp lr pkU verQ A N σ hver E g hw)) ?_
  rw [Finset.sum_disjSum, Finset.sum_disjSum]
  have h1 : ∀ k ∈ Finset.range N, prExp lr pkU verQ A N σ (.inl (.inl k)) ≤
      epsIss (N * (eA + eVR lr pkU eV)) (N • (qA + qV)) := fun k hk => by
    unfold prExp exps
    rw [prEvent_map_decide]
    exact pr_failI_le lr pkU verQ A N σ hver hqA hnA heA (Finset.mem_range.1 hk)
  have h2 : ∀ k ∈ Finset.range N, prExp lr pkU verQ A N σ (.inl (.inr k)) ≤
      epsSpend (N * (eA + eVR lr pkU eV)) (N * (nA + nV)) (N • (qA + qV)) := fun k hk => by
    unfold prExp exps
    rw [prEvent_map_decide]
    exact pr_failS_le lr pkU verQ A N σ hver hqA hnA heA hdig (Finset.mem_range.1 hk)
  have h3 : prExp lr pkU verQ A N σ (.inr true) + prExp lr pkU verQ A N σ (.inr false) =
      forgeAdv lr pkU verQ A N σ + collAdv lr pkU verQ A N σ := by
    unfold prExp exps
    rw [prEvent_map_decide, prEvent_map_decide]
    rfl
  have s1 := Finset.sum_le_sum h1
  have s2 := Finset.sum_le_sum h2
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at s1 s2
  unfold prExp at s1 s2 h3
  refine le_trans (add_le_add (add_le_add s1 s2) (le_of_eq ?_)) (le_of_eq (add_assoc _ _ _).symm)
  rw [Fintype.sum_bool]
  exact h3

/-- The Issuer's verifications re-run with the cipher as queries (`ROM/VerifierIC.lean`). -/
def verQL (st : Statement) (pf : ByteArray) : OracleComp specIC Bool :=
  (·.accept) <$> verifyIC CrtGen.tables st pf

/-- **Theorem 1 (balance), with no hypothesis on the verifier**: `balance_le` with the
cipher-querying verifier `verifyIC` (`verifierIC_verifyIC`): per verification `verifierQueriesIC`
hash queries per kind, `verifierTotal + 2` in all, and `cipherCount` cipher queries. -/
theorem balance_le_lean (A : RoundAdv S (Op Z) Resp) (N : ℕ) (σ : Signer)
    (hdig : pkU.digest.size = 32) {qA : Kind → ℕ} {nA eA : ℕ}
    (hqA : ∀ s, IsKindQueryBoundIC (A.next s) qA)
    (hnA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isLeft = true) nA)
    (heA : ∀ s, IsQueryBoundP (A.next s) (fun t => t.isRight = true) eA) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (balQ lr pkU A N σ E)).run' ∅}[
        Win r.2.2] ≤
      N * epsIss (N * (eA + eVR lr pkU cipherCount)) (N • (qA + verifierQueriesIC)) +
        N * epsSpend (N * (eA + eVR lr pkU cipherCount)) (N * (nA + (verifierTotal + 2)))
          (N • (qA + verifierQueriesIC)) +
        forgeAdv lr pkU verQL A N σ + collAdv lr pkU verQL A N σ :=
  balance_le lr pkU verQL A N σ hdig (verifierIC_verifyIC CrtGen.tables) hqA hnA heA

end VoleMole.ROM.IC.RatBalance
