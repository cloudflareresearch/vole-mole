import VoleMole.ROM.ExtractReduce
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

`balance_le`: `Pr[win] ≤ N·ε_iss + N·ε_spend + Adv^{uf-tag}(B) + Adv^{coll}(C)`, where
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

## The remaining hypothesis

The `j`-th prover must re-run the Issuer's verifications as queries to the cipher, so that the
straight-line extractor sees them (as the paper's extractor reads the Issuer's queries). The
executable verifier reads the cipher as a table (`icPrg E.cipher`), so the theorem takes a
cipher-querying implementation of it as the hypothesis `VerifierIC` (agreement with `verify` on
every table, and query bounds). Nothing probabilistic is assumed about it.
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

/-- The credits issued per context: `T_init` of every accepted issuance. -/
def issuedOf : List (Op Z × Resp) → List (Context × ℕ)
  | [] => []
  | (.issue _ tInit ctx, .inl (.ok (some _))) :: tr => (ctx, tInit.toNat) :: issuedOf tr
  | _ :: tr => issuedOf tr

/-- The credits spent per context: `d` of every accepted spend. -/
def spentOf : List (Op Z × Resp) → List (Context × ℕ)
  | [] => []
  | (.spend _ ctx _, .inr (.ok (some out))) :: tr => (ctx, out.d.toNat) :: spentOf tr
  | _ :: tr => spentOf tr

/-- The refunds granted per context: `x'` of every accepted spend. -/
def refundedOf : List (Op Z × Resp) → List (Context × ℕ)
  | [] => []
  | (.spend _ ctx refund, .inr (.ok (some _))) :: tr => (ctx, refund.toNat) :: refundedOf tr
  | _ :: tr => refundedOf tr

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

end VoleMole.ROM.IC.RatBalance
