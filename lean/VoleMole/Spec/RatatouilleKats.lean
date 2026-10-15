import VoleMole.Spec.Common
import VoleMole.Spec.Ratatouille

/-!
# Known-answer cross-check of `Spec.Ratatouille` (run by `lake exe spec_kats`)

Reads `tests/ratatouille/ratatouille_kat.txt` (`tests/ratatouille/gen_ratatouille_kat.cpp`; one
record per issuance followed by one record per spend, each spend spending the previous change
token) and the expanded public maps `test`, `alt61`, `alt62` of the keys with secret key
`filled(0x60)`, `filled(0x61)`, `filled(0x62)` (generated in Lean by `Spec/Kats.lean`).

For each case it runs the model's client and Issuer code, with abstract primitives instantiated
by the file's values (the prover returns the file's proof bytes, the verifier accepts, the signer
returns the file's signature), and compares:

* `expandSeed` against `nf`, `r`, `nf_next`, `r_next` (SHAKE128);
* `com` against `commitment`, and the witness layouts against `issue_witness`, `spend_witness`;
* `issueRequestWithSeed` / `spendRequestWithSeed` against `issue_request` / `spend_request`
  (everything but the proof bytes is recomputed: `c`, `nf`, `⟨d⟩₈`, `c'`), including the
  client's validity check `P(s) = Tag(Com(nf, ctx, t, r), x)` of the token being spent and the
  credit arithmetic (`t_next`);
* `issueResponse` / `spendResponse` against the responses (framing `⟨x'⟩₈ ‖ s'`, the returned
  `nf` and `d`), and `finalizeIssue` / `finalizeSpend`, i.e. `P(s) = Tag(c, x)` with the real
  public map, giving the change token `(t_next, refund)`;
* negative checks: a response with a flipped refund bit or signature bit is rejected by
  `finalizeSpend`, and a spend exceeding the balance is rejected by `spendRequestWithSeed`.
-/

namespace VoleMole.Spec.Ratatouille.Kats

open VoleMole.Spec.Ratatouille

abbrev Rec := VoleMole.Spec.KatRecord

/-- A byte list of the right length as a vector. -/
def toVec (what : String) (b : List UInt8) (n : ℕ) : Except String (Bytes n) :=
  if h : b.toArray.size = n then .ok ⟨b.toArray, h⟩
  else .error s!"field `{what}`: expected {n} bytes, got {b.length}"

def field (r : Rec) (k : String) (n : ℕ) : Except String (Bytes n) := do
  toVec k (← r.bytes k) n

def credits (r : Rec) (k : String) : Except String Credits := do
  let v ← r.nat k
  if v < 2 ^ 64 then pure v.toUInt64 else throw s!"field `{k}`: out of range"

/-- An expanded public map as `ℕ → GF256`. -/
def pkOf (b : ByteArray) : PublicKey := fun i => if h : i < b.size then ⟨b[i]⟩ else 0

/-- Primitives that return the given proofs and signature and accept every proof. -/
def katPrim (pk : PublicKey) (pfIss : IssueProof Sizes.main) (pfSpend : SpendProof Sizes.main)
    (sig : Preimage) : Prim Sizes.main Unit where
  pk _ := pk
  derive _ _ := some sig
  proveIssue _ _ _ := some pfIss
  verifyIssue _ _ := true
  proveSpend _ _ _ := some pfSpend
  verifySpend _ _ := true

def hex {n : ℕ} (v : Bytes n) : String := VoleMole.Arith.Hex.bytesToHex v.toList

def chk {n : ℕ} (what : String) (got want : Bytes n) : List String :=
  if got = want then [] else [s!"{what}: got {hex got}, want {hex want}"]

def chkL (what : String) (got want : List UInt8) : List String :=
  if got = want then [] else
    [s!"{what}: got {VoleMole.Arith.Hex.bytesToHex got}, want {VoleMole.Arith.Hex.bytesToHex want}"]

def chkB (what : String) (b : Bool) : List String := if b then [] else [what]

/-- The issuance record: returns the errors and the issued token. -/
def checkIssue (keys : Std.HashMap String ByteArray) (r : Rec) :
    Except String (List String × PublicKey × Context × TokenS) := do
  let seed ← field r "issue_seed" 32
  let ctx ← field r "ctx_iss" 16
  let tInit ← credits r "t_init"
  let sk ← r.bytes "issuer_sk"
  let start := sk.headD 0
  unless sk = (List.range 32).map fun i => (start.toNat + i).toUInt8 do
    throw "issuer_sk is not filled(b)"
  let name := match start with
    | 0x60 => "test"
    | 0x61 => "alt61"
    | 0x62 => "alt62"
    | _ => ""
  let some pkb := keys[name]? | throw s!"no key for issuer_sk {start} (`{name}`)"
  let pk := pkOf pkb
  let nf ← field r "nf" 24
  let rr ← field r "r" 16
  let c ← field r "commitment" 32
  let req ← field r "issue_request" 7032
  let s ← field r "issue_response" 119
  let wit ← r.bytes "issue_witness"
  let mut errs : List String := []
  let (nf₀, r₀, _) := expandSeed issueSeedDst seed
  errs := errs ++ chk "nf" nf₀ nf ++ chk "r" r₀ rr
  errs := errs ++ chk "commitment" (com nf ctx tInit rr) c
  errs := errs ++ chkL "issue_witness" (encodeIssueWitness nf ctx tInit rr) wit
  let P := katPrim pk (issueReqProof req) (Vector.replicate 17319 0) s
  match issueRequestWithSeed P tInit ctx seed with
  | .error e => throw s!"issueRequestWithSeed failed: {repr e}"
  | .ok (pt, req') =>
    errs := errs ++ chk "issue_request" req' req ++ chk "pending c" pt.c c
    match issueResponse P () req tInit ctx with
    | .ok (some s') => errs := errs ++ chk "issue_response" s' s
    | _ => errs := errs ++ ["issueResponse did not answer"]
    errs := errs ++ chkB "issueResponse accepted t_init = 0"
      (match issueResponse P () req 0 ctx with | .error .invalidArgument => true | _ => false)
    match finalizeIssue pk (some pt) s with
    | (none, .ok (some τ)) =>
      errs := errs ++ chkB "token (t_init, 0)" (τ.t == tInit && τ.x == 0)
      return (errs, pk, ctx, τ)
    | _ => throw "finalizeIssue rejected the issue response (P(s) ≠ Tag(c, 0))"

/-- One spend record: returns the errors and the change token. -/
def checkSpend (pk : PublicKey) (ctx : Context) (τ : TokenS) (r : Rec) :
    Except String (List String × TokenS) := do
  let seed ← field r "spend_seed" 32
  let d ← credits r "d"
  let refund ← credits r "refund"
  let nf' ← field r "nf_next" 24
  let t' ← credits r "t_next"
  let r' ← field r "r_next" 16
  let wit ← r.bytes "spend_witness"
  let req ← field r "spend_request" 17383
  let resp ← field r "spend_response" 127
  let mut errs : List String := []
  let (nf₀, r₀, _) := expandSeed spendSeedDst seed
  errs := errs ++ chk "nf_next" nf₀ nf' ++ chk "r_next" r₀ r'
  errs := errs ++ chkB s!"t_next: clientCheck gives {repr (clientCheck τ.t τ.x d)}, want {t'}"
    (clientCheck τ.t τ.x d == some t')
  errs := errs ++ chkL "spend_witness"
    (encodeSpendWitness τ.nf ⟨τ.t, τ.r, τ.x, τ.s, nf', t', r'⟩ d ctx) wit
  let q := SpendReq.parse (Z := Sizes.main) req
  let P := katPrim pk (Vector.replicate 7000 0) q.proof (respSig resp)
  match spendRequestWithSeed P pk (some τ) d ctx seed with
  | (some _, _) => throw "spendRequestWithSeed did not consume the token"
  | (none, .error e) => throw s!"spendRequestWithSeed failed: {repr e}"
  | (none, .ok (ps, req')) =>
    errs := errs ++ chk "spend_request" req' req ++ chk "pending nf'" ps.nf nf'
    errs := errs ++ chkB "pending t'" (ps.t == t') ++ chk "pending r'" ps.r r'
    errs := errs ++ chk "pending c'" ps.c (com nf' ctx t' r')
    -- Over-spending is rejected and keeps the token.
    if τ.t.toNat + τ.x.toNat < 2 ^ 64 - 1 then
      let dBad : Credits := τ.t + τ.x + 1
      errs := errs ++ chkB "spending t + x + 1 was not rejected"
        (match spendRequestWithSeed P pk (some τ) dBad ctx seed with
          | (some _, .error .invalidArgument) => true
          | _ => false)
    match spendResponse P () req ctx refund with
    | .ok (some out) =>
      errs := errs ++ chk "spend_response" out.response resp ++ chk "returned nf" out.nf τ.nf
      errs := errs ++ chkB "returned d" (out.d == d)
    | _ => errs := errs ++ ["spendResponse did not answer"]
    errs := errs ++ chkB "response refund" (respRefund resp == refund)
    -- Tampered responses are rejected (and still consume the pending spend, F3).
    let flipRefund := resp.set 0 (resp[0] ^^^ 1)
    let flipSig := resp.set 8 (resp[8] ^^^ 1)
    errs := errs ++ chkB "finalizeSpend accepted a modified refund"
      (match finalizeSpend pk (some ps) flipRefund with | (none, .ok none) => true | _ => false)
    errs := errs ++ chkB "finalizeSpend accepted a modified signature"
      (match finalizeSpend pk (some ps) flipSig with | (none, .ok none) => true | _ => false)
    match finalizeSpend pk (some ps) resp with
    | (none, .ok (some τ')) =>
      errs := errs ++ chkB "change token (t_next, refund)" (τ'.t == t' && τ'.x == refund)
      return (errs, τ')
    | _ => throw "finalizeSpend rejected the spend response (P(s') ≠ Tag(c', x'))"

/-- Check the whole file; returns one `(label, errors)` per case. -/
def checkFile (keys : Std.HashMap String ByteArray) (recs : Array Rec) : List (String × List String) :=
  Id.run do
    let mut out : List (String × List String) := []
    let mut i := 0
    let mut j := 0
    let mut cases := 0
    while i < recs.size do
      let r := recs[i]!
      let label := s!"ratatouille_kat.txt case {cases}"
      cases := cases + 1
      match checkIssue keys r, r.nat "spend_count" with
      | .ok (errs, pk, ctx, τ), .ok n =>
        let mut errs := errs
        let mut τ := τ
        j := 0
        while j < n do
          match checkSpend pk ctx τ (recs[i + 1 + j]?.getD #[]) with
          | .ok (e, τ') => errs := errs ++ e.map (s!"spend {j}: " ++ ·); τ := τ'
          | .error e => errs := errs ++ [s!"spend {j}: {e}"]
          j := j + 1
        out := out ++ [(s!"{label} (issue + {n} spends)", errs)]
        i := i + 1 + n
      | .error e, _ | _, .error e =>
        out := out ++ [(label, [e])]
        i := recs.size
    return out

end VoleMole.Spec.Ratatouille.Kats
