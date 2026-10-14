import VoleMole.Spec.PomFRIT
import VoleMole.Spec.Moussaka
import VoleMole.Spec.RatatouilleKats

/-!
# Known-answer cross-checks of the protocol specs against the C++ (`lake exe spec_kats`)

Usage: `lake exe spec_kats [REPO_ROOT]` (default `..`, i.e. run from `lean/`). Reads

* `tests/moussaka/moussaka_kat.txt` (`tests/moussaka/gen_moussaka_kat.cpp`),
* `tests/pomfrit/pomfrit_kat.txt` (`tests/pomfrit/gen_pomfrit_kat.cpp`),
* `tests/ratatouille/ratatouille_kat.txt` (`tests/ratatouille/gen_ratatouille_kat.cpp`; checked by
  `Spec/RatatouilleKats.lean`, see there),
* `lean/vectors/uov_keys.txt` (expanded public maps, `tests/arith/dump_arith_vectors.cpp`):
  key `test` is the key pair with secret key `filled(0x60)`, `alt61` and `alt62` the ones with
  `filled(0x61)` and `filled(0x62)`.

and recomputes with `Spec.Moussaka` / `Spec.PomFRIT` every field that does not depend on the
VOLEitH internals: seed expansions, commitments, witness layouts, request/response framing,
`P(s) = t` on the responses, the refresher commitment, `hash_to_target` and the masked target. The
proof bytes themselves are abstract; for PomFRIT, `chal1` (an output of the abstract
`voleith_vole_reconstruct`) is taken from the file.
-/

namespace VoleMole.Spec.Kats

open VoleMole.Arith VoleMole.Spec

/-- `filled<32>(start)`. -/
def filled (start : ℕ) (n : ℕ := 32) : Bytes := (List.range n).map fun i => (start + i).toUInt8

/-- Run the checks of one record, returning the error messages. -/
def runChecks (f : Except String (List String)) : List String :=
  match f with
  | .ok e => e
  | .error e => [e]

def report (what : String) (errs : List String) : IO Bool := do
  if errs.isEmpty then
    IO.println s!"ok    {what}"
    return true
  else
    IO.println s!"FAIL  {what}"
    for e in errs.take 10 do IO.println s!"      {e}"
    return false

/-- A test-only prover that writes an all-zero proof: used to exercise the framing of
`redeemRequest` without the VOLEitH internals. -/
def zeroRedeemProver : Moussaka.NIZK Moussaka.RedeemInstance :=
  ⟨fun _ _ _ => List.replicate Moussaka.redeemProofBytes 0, fun _ _ => false⟩

/-! ## Moussaka -/

def checkMoussaka (keys : Std.HashMap String ByteArray) (r : KatRecord) :
    Except String (List String) := do
  let seed ← r.bytes "issue_seed"
  let ctxIss ← r.bytes "ctx_iss"
  let ctxRed ← r.bytes "ctx_red"
  let cd ← r.bytes "challenge_digest"
  let n ← r.nat "anchor_count"
  let issuer ← r.nat "issuer"
  let sks := r.getAll "anchor_sk"
  let (nf, rr, _) := Moussaka.expandIssueSeed seed
  let t := Moussaka.com nf ctxIss ctxRed rr
  let req ← r.bytes "issue_request"
  let s ← r.bytes "issue_response"
  let rreq ← r.bytes "redeem_request"
  let mut errs : List String := []
  errs := errs ++ checkEq "nf" nf (← r.bytes "nf")
  errs := errs ++ checkEq "r" rr (← r.bytes "r")
  errs := errs ++ checkEq "commitment" t (← r.bytes "commitment")
  errs := errs ++ checkEq "issue_witness" (Moussaka.encodeIssueWitness nf ctxIss ctxRed rr)
    (← r.bytes "issue_witness")
  if req.length ≠ Moussaka.issueRequestBytes then errs := errs ++ ["issue_request: bad length"]
  errs := errs ++ checkEq "issue_request[0..45)" (req.take uovM) t
  errs := errs ++ checkEq "redeem_witness"
    (Moussaka.encodeRedeemWitness nf ctxIss ctxRed rr s issuer) (← r.bytes "redeem_witness")
  if rreq.length ≠ Moussaka.redeemRequestBytes then errs := errs ++ ["redeem_request: bad length"]
  errs := errs ++ checkEq "redeem_request[0..24)" (rreq.take Moussaka.nfBytes) nf
  errs := errs ++ checkEq "redeemed_nf" (← r.bytes "redeemed_nf") nf
  if sks.length ≠ n then errs := errs ++ ["anchor_sk count ≠ anchor_count"]
  -- The issuer's key is `test` (filled(0x60)): check P(s) = t through finalizeIssue.
  if sks[issuer]? ≠ some (Hex.bytesToHex (filled 0x60)) then
    errs := errs ++ ["issuer key is not filled(0x60)"]
  let some test := keys["test"]? | throw "uov_keys.txt has no key `test`"
  let pkTest := UOVKey.ofExpanded [] test
  let pending : Moussaka.PendingToken := ⟨nf, rr, ctxIss, ctxRed, t⟩
  match Moussaka.finalizeIssue pkTest pending s with
  | none => errs := errs ++ ["finalizeIssue: P(s) ≠ t for the issuer key"]
  | some tok =>
    -- Redeem framing with the issuer at its index (other Anchors as placeholders with distinct
    -- digests; only the indicated key is evaluated).
    let anchorKeys := (List.range n).map fun u =>
      if u = issuer then { pkTest with digest := [u.toUInt8] } else ⟨[u.toUInt8], fun _ => 0⟩
    match Moussaka.AnchorSet.mk? anchorKeys with
    | .error _ => errs := errs ++ ["AnchorSet.mk? rejected the Anchor Set"]
    | .ok A =>
      match Moussaka.redeemRequest zeroRedeemProver tok A issuer ctxIss ctxRed cd [] with
      | .ok q =>
        errs := errs ++ checkEq "redeemRequest framing" (q.take Moussaka.nfBytes) (rreq.take Moussaka.nfBytes)
        if q.length ≠ Moussaka.redeemRequestBytes then errs := errs ++ ["redeemRequest: bad length"]
      | .error _ => errs := errs ++ ["redeemRequest rejected the honest token"]
      if (Moussaka.redeemRequest zeroRedeemProver tok A n ctxIss ctxRed cd []) matches .ok _ then
        errs := errs ++ ["redeemRequest accepted an out-of-range index"]
  -- A different key (`alt61`, filled(0x61)) does not verify the token.
  if let some alt := keys["alt61"]? then
    if (UOVKey.ofExpanded [] alt).eval s = t then errs := errs ++ ["alt61 verifies the token"]
  return errs

/-! ## PomFRIT -/

def checkPomfritHeader (r : KatRecord) : Except String (List String) := do
  let mut errs : List String := []
  for (k, v) in [("signature_bytes", PomFRIT.sigBytes), ("proof_bytes", PomFRIT.proofBytes),
      ("refresher_bytes", PomFRIT.refresherBytes), ("vole_check_proof_offset", PomFRIT.offVoleCheck),
      ("vole_check_proof_bytes", PomFRIT.voleCheckBytes), ("correction_offset", PomFRIT.offCorrection),
      ("correction_bytes", PomFRIT.correctionBytes)] do
    if (← r.nat k) ≠ v then errs := errs ++ [s!"{k}: spec has {v}"]
  errs := errs ++ checkEq "pk_digest = SHAKE256(pk)" (shake256B (← r.bytes "pk") digestBytes)
    (← r.bytes "pk_digest")
  errs := errs ++ checkEq "sk" (← r.bytes "sk") (filled 0x60)
  return errs

def checkPomfrit (pk : UOVKey) (r : KatRecord) : Except String (List String) := do
  let seed ← r.bytes "seed"
  let msg ← r.bytes "msg"
  let t ← r.bytes "request"
  let s ← r.bytes "response"
  let chal1 ← r.bytes "chal1"
  let sig ← r.bytes "signature"
  let (_, refresher, rr) := PomFRIT.expandSeed pk.digest msg seed
  let h := PomFRIT.hashToTarget pk.digest chal1 sig msg
  let mut errs : List String := []
  if sig.length ≠ PomFRIT.sigBytes then errs := errs ++ ["signature: bad length"]
  errs := errs ++ checkEq "refresher" (PomFRIT.sigRefresher sig) refresher
  errs := errs ++ checkEq "refresher_com" (PomFRIT.sigRefresherCom sig)
    (PomFRIT.commitRefresher refresher)
  errs := errs ++ checkEq "request = H_T(...) ⊕ r" (xorBytes h rr) t
  if pk.eval s ≠ t then errs := errs ++ ["P(s) ≠ t"]
  if s.length ≠ uovN then errs := errs ++ ["response: bad length"]
  -- `verify` with the abstract verifier instantiated by the file's chal1 and a final check that the
  -- target it is handed is the Client's h = t ⊕ r.
  let V : PomFRIT.Verifier :=
    ⟨fun _ _ => some chal1, fun _ _ _ h' _ => decide (h' = xorBytes t rr)⟩
  if !PomFRIT.verify V pk msg sig then errs := errs ++ ["verify (front end) rejected"]
  if PomFRIT.verify V pk (msg ++ [0]) sig then errs := errs ++ ["verify accepted another message"]
  let sig' := sig.set (PomFRIT.offCorrection + 3) ((sig.getD (PomFRIT.offCorrection + 3) 0) ^^^ 1)
  if PomFRIT.verify V pk msg sig' then errs := errs ++ ["verify accepted a modified d[0..M)"]
  let sig'' := sig.set (PomFRIT.sigBytes - 1) ((sig.getD (PomFRIT.sigBytes - 1) 0) ^^^ 1)
  if PomFRIT.verify V pk msg sig'' then errs := errs ++ ["verify accepted a modified refresher"]
  return errs

def main (args : List String) : IO UInt32 := do
  let root := args.headD ".."
  let mut keys : Std.HashMap String ByteArray := {}
  for line in (← IO.FS.readFile s!"{root}/lean/vectors/uov_keys.txt").splitOn "\n" do
    if let ["key", name, hex] := line.splitOn " " then
      match Hex.decodeByteArray? hex with
      | some b => keys := keys.insert name b
      | none => throw (IO.userError s!"uov_keys.txt: bad hex for key {name}")
  let mut ok := true
  -- Moussaka.
  let mous := parseKat (← IO.FS.readFile s!"{root}/tests/moussaka/moussaka_kat.txt")
  if mous.size ≠ 3 then ok := false; IO.println s!"FAIL  moussaka_kat.txt: {mous.size} records"
  for h : i in [0:mous.size] do
    ok := (← report s!"moussaka_kat.txt case {i}" (runChecks (checkMoussaka keys mous[i]))) && ok
  -- PomFRIT.
  let pom := parseKat (← IO.FS.readFile s!"{root}/tests/pomfrit/pomfrit_kat.txt")
  match pom[0]? with
  | none => ok := false; IO.println "FAIL  pomfrit_kat.txt: empty"
  | some hdr =>
    ok := (← report "pomfrit_kat.txt layout and key digest" (runChecks (checkPomfritHeader hdr))) && ok
    let some test := keys["test"]? | throw (IO.userError "uov_keys.txt has no key `test`")
    let dig ← IO.ofExcept (hdr.bytes "pk_digest")
    let pk := UOVKey.ofExpanded dig test
    if pom.size ≠ 4 then ok := false; IO.println s!"FAIL  pomfrit_kat.txt: {pom.size} records"
    for h : i in [1:pom.size] do
      ok := (← report s!"pomfrit_kat.txt case {i - 1}" (runChecks (checkPomfrit pk pom[i]))) && ok
  -- Ratatouille.
  let rata := parseKat (← IO.FS.readFile s!"{root}/tests/ratatouille/ratatouille_kat.txt")
  let rataResults := Ratatouille.Kats.checkFile keys rata
  if rataResults.length ≠ 3 then
    ok := false; IO.println s!"FAIL  ratatouille_kat.txt: {rataResults.length} cases"
  for (label, errs) in rataResults do
    ok := (← report label errs) && ok
  IO.println (if ok then "all spec known answers match" else "MISMATCHES")
  return if ok then 0 else 1

end VoleMole.Spec.Kats

def main (args : List String) : IO UInt32 := VoleMole.Spec.Kats.main args
