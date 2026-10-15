import VoleMole.Spec.PomFRIT
import VoleMole.Spec.Moussaka
import VoleMole.Spec.RatatouilleKats
import VoleMole.Verifier.Relations
import VoleMole.Verifier.CrtGen

/-!
# Known-answer cross-checks of the protocol specs against the C++ (`lake exe spec_kats`)

Usage: `lake exe spec_kats [REPO_ROOT]` (default `..`, i.e. run from `lean/`). Reads

* `tests/moussaka/moussaka_kat.txt` (`tests/moussaka/gen_moussaka_kat.cpp`),
* `tests/pomfrit/pomfrit_kat.txt` (`tests/pomfrit/gen_pomfrit_kat.cpp`),
* `tests/ratatouille/ratatouille_kat.txt` (`tests/ratatouille/gen_ratatouille_kat.cpp`; checked by
  `Spec/RatatouilleKats.lean`, see there),
and recomputes with `Spec.Moussaka` / `Spec.PomFRIT` every field that does not depend on the
VOLEitH internals: seed expansions, commitments, witness layouts, request/response framing,
`P(s) = t` on the responses, the refresher commitment, `hash_to_target` and the masked target. The
proof bytes themselves are abstract; for PomFRIT, `chal1` (an output of the abstract
`voleith_vole_reconstruct`) is taken from the file.

UOV public keys are generated from the compact secret keys in Lean (`Verifier.UovPk.ofSecret`:
pqov's key generation and `expand_pk`, `Verifier/Keygen.lean`): key `test` has secret key
`filled(0x60)`, `alt61` and `alt62` have `filled(0x61)` and `filled(0x62)`. If
`lean/vectors/uov_keys.txt` (expanded public maps, `tests/arith/dump_arith_vectors.cpp`) exists,
the generated `test`, `alt61`, `alt62` are compared with it; it is not needed.

Moussaka redemption depends on the whole Anchor Set only through the proof's instance (the
digests of all Anchor keys, `RedeemInstance.encode`). So the redemption request is checked by
`finalizeRedeem` with the abstract verifier instantiated by the Lean VOLEitH verifier
(`Verifier.verify` on `Verifier.moussakaRedeem`, CRT tables from `Verifier.CrtGen`), under the
Anchor Set generated from the `anchor_sk` fields: the proof must be accepted, which checks every
Anchor's digest, and rejected when two non-issuer Anchors are swapped.
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

/-- Moussaka's redemption NIZK with the Lean VOLEitH verifier: Anchor keys are identified by their
digests in `pks` (a key not in `pks` fails verification). Proving is not modelled. -/
def verifierRedeem (pks : List Verifier.UovPk) : Moussaka.NIZK Moussaka.RedeemInstance :=
  ⟨fun _ _ _ => [], fun pf x =>
    match x.anchors.mapM fun k => pks.find? (·.digest.toList == k.digest) with
    | some ps => (Verifier.verify Verifier.Hashes.shake Verifier.CrtGen.tables
        (Verifier.moussakaRedeem ps (Verifier.toBA x.nf) (Verifier.toBA x.ctxIss)
          (Verifier.toBA x.ctxRed) (Verifier.toBA x.challengeDigest)) (Verifier.toBA pf)).accept
    | none => false⟩

/-- `pks`: compact secret key (hex) ↦ generated public key, for every `anchor_sk`. -/
def checkMoussaka (keys : Std.HashMap String ByteArray) (pks : Std.HashMap String Verifier.UovPk)
    (swapCheck : Bool) (r : KatRecord) : Except String (List String) := do
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
  let some test := keys["test"]? | throw "no key `test`"
  let pkTest := UOVKey.ofExpanded [] test
  -- The Anchor Set, generated from the secret keys.
  let some anchors := sks.mapM (pks[·]?) | throw "anchor_sk without a generated key"
  let pending : Moussaka.PendingToken := ⟨nf, rr, ctxIss, ctxRed, t⟩
  match Moussaka.finalizeIssue pkTest pending s with
  | none => errs := errs ++ ["finalizeIssue: P(s) ≠ t for the issuer key"]
  | some tok =>
    match Moussaka.AnchorSet.mk? (anchors.map Verifier.UovPk.toSpec) with
    | .error _ => errs := errs ++ ["AnchorSet.mk? rejected the Anchor Set"]
    | .ok A =>
      match Moussaka.redeemRequest zeroRedeemProver tok A issuer ctxIss ctxRed cd [] with
      | .ok q =>
        errs := errs ++ checkEq "redeemRequest framing" (q.take Moussaka.nfBytes) (rreq.take Moussaka.nfBytes)
        if q.length ≠ Moussaka.redeemRequestBytes then errs := errs ++ ["redeemRequest: bad length"]
      | .error _ => errs := errs ++ ["redeemRequest rejected the honest token"]
      if (Moussaka.redeemRequest zeroRedeemProver tok A n ctxIss ctxRed cd []) matches .ok _ then
        errs := errs ++ ["redeemRequest accepted an out-of-range index"]
      -- The redemption proof, verified under the generated Anchor Set (all digests).
      let VR := verifierRedeem anchors
      if Moussaka.finalizeRedeem VR A rreq ctxIss ctxRed cd ≠ some nf then
        errs := errs ++ ["finalizeRedeem (Lean verifier) rejected the redeem request"]
      -- Two non-issuer Anchors swapped: rejected (if `swapCheck`; each verification costs
      -- about a second per Anchor).
      match (List.range n).filter (· ≠ issuer) with
      | u :: w :: _ =>
        if swapCheck then
          let dummy : Verifier.UovPk := ⟨.empty, .empty⟩
          let swapped := (anchors.set u (anchors.getD w dummy)).set w (anchors.getD u dummy)
          match Moussaka.AnchorSet.mk? (swapped.map Verifier.UovPk.toSpec) with
          | .ok A' =>
            if (Moussaka.finalizeRedeem VR A' rreq ctxIss ctxRed cd).isSome then
              errs := errs ++ [s!"finalizeRedeem accepted with Anchors {u} and {w} swapped"]
          | .error _ => errs := errs ++ ["AnchorSet.mk? rejected the swapped Anchor Set"]
      | _ => pure ()
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
  -- UOV keys, generated in Lean; compared with uov_keys.txt if present.
  let t0 ← IO.monoMsNow
  let mut keys : Std.HashMap String ByteArray := {}
  for (name, start) in [("test", 0x60), ("alt61", 0x61), ("alt62", 0x62)] do
    keys := keys.insert name (Verifier.UovPk.ofSecret (Verifier.toBA (filled start))).expanded
  let mut ok := true
  let path := s!"{root}/lean/vectors/uov_keys.txt"
  if ← System.FilePath.pathExists path then
    let mut errs : List String := []
    let mut n := 0
    for line in (← IO.FS.readFile path).splitOn "\n" do
      if let ["key", name, hex] := line.splitOn " " then
        n := n + 1
        if keys[name]?.map (·.toList) ≠ (Hex.decodeByteArray? hex).map (·.toList) then
          errs := errs ++ [s!"key {name} differs"]
    if n = 0 then errs := errs ++ ["no keys"]
    ok := (← report "generated UOV keys = uov_keys.txt (test, alt61, alt62)" errs) && ok
  else IO.println "      (no lean/vectors/uov_keys.txt: generated keys not compared with the C++)"
  let mous := parseKat (← IO.FS.readFile s!"{root}/tests/moussaka/moussaka_kat.txt")
  let mut pks : Std.HashMap String Verifier.UovPk := {}
  for r in mous do
    for sk in r.getAll "anchor_sk" do
      if !pks.contains sk then
        let some b := Hex.decodeByteArray? sk | throw (IO.userError s!"bad anchor_sk {sk}")
        pks := pks.insert sk (Verifier.UovPk.ofSecret b)
  IO.println s!"      UOV key generation: {pks.size + 3} keys ({(← IO.monoMsNow) - t0} ms)"
  -- Moussaka.
  if mous.size ≠ 3 then ok := false; IO.println s!"FAIL  moussaka_kat.txt: {mous.size} records"
  for h : i in [0:mous.size] do
    let t1 ← IO.monoMsNow
    let errs ← IO.lazyPure fun _ =>
      runChecks (checkMoussaka keys pks ((mous[i].getAll "anchor_sk").length ≤ 3) mous[i])
    ok := (← report s!"moussaka_kat.txt case {i} ({(← IO.monoMsNow) - t1} ms)" errs) && ok
  -- PomFRIT.
  let pom := parseKat (← IO.FS.readFile s!"{root}/tests/pomfrit/pomfrit_kat.txt")
  match pom[0]? with
  | none => ok := false; IO.println "FAIL  pomfrit_kat.txt: empty"
  | some hdr =>
    ok := (← report "pomfrit_kat.txt layout and key digest" (runChecks (checkPomfritHeader hdr))) && ok
    let some test := keys["test"]? | throw (IO.userError "no key `test`")
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
