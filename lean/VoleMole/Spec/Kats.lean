import VoleMole.Spec.PomFRITLayout
import VoleMole.Spec.Moussaka
import VoleMole.Spec.MoussakaUnbound
import VoleMole.Spec.RatatouilleKats
import VoleMole.Verifier.Relations
import VoleMole.Verifier.CrtGen
import VoleMole.Spec.PqovSignerExec

/-!
# Known-answer cross-checks of the protocol specs against the C++ (`lake exe spec_kats`)

Usage: `lake exe spec_kats [REPO_ROOT]` (default `..`, i.e. run from `lean/`). Reads

* `tests/ihat/ihat_kat.txt` (`tests/ihat/gen_ihat_kat.cpp`),
* `tests/ihat/unbound_ihat_kat.txt` (unbound tokens: seed expansion, `UCom`, `Derive`, both
  witness encodings and the request framing, with `Spec.MoussakaUnbound`),
* `tests/pomfrit/pomfrit_kat.txt` (`tests/pomfrit/gen_pomfrit_kat.cpp`),
* `tests/act/act_kat.txt` (`tests/act/gen_act_kat.cpp`; checked by
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

pqov's signer model (`Spec.Pqov.deriveRef`, `Spec/PqovSigner.lean`: the linear system from the
public map's polar form) is run, in its executable form `Spec.Pqov.deriveRefExec`
(`Spec/PqovSignerExec.lean`), on the test key generated in Lean with the oil matrix of its seed, at
every Moussaka issuance and PomFRIT request target of the files: its output must equal the C++
`derive_preimage` response byte for byte (and satisfy `P(s) = t`).
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

/-- One record of `unbound_ihat_kat.txt`: an unbound token and its redemptions. -/
def checkMoussakaUnbound (r : KatRecord) : Except String (List String) := do
  let hex (k : String) (i : ℕ) : Except String Bytes := do
    let some v := (r.getAll k)[i]? | throw s!"missing field `{k}` #{i}"
    let some b := Hex.decode? v | throw s!"field `{k}` #{i}: bad hex"
    pure b
  let ctxIss ← r.bytes "ctx_iss"
  let issuer ← r.nat "issuer"
  let (k, rr, _) := MoussakaUnbound.expandIssueSeed (← r.bytes "issue_seed")
  let t := MoussakaUnbound.ucom k ctxIss rr
  let req ← r.bytes "issue_request"
  let s ← r.bytes "issue_response"
  let mut errs : List String := []
  errs := errs ++ checkEq "nf_key" k (← r.bytes "nf_key")
  errs := errs ++ checkEq "r" rr (← r.bytes "r")
  errs := errs ++ checkEq "commitment" t (← r.bytes "commitment")
  errs := errs ++ checkEq "issue_witness" (MoussakaUnbound.encodeIssueWitness k ctxIss rr)
    (← r.bytes "issue_witness")
  if req.length ≠ uovM + 6864 then errs := errs ++ ["issue_request: bad length"]
  errs := errs ++ checkEq "issue_request[0..45)" (req.take uovM) t
  let n := (r.getAll "redeem_seed").length
  if n = 0 then errs := errs ++ ["no redemptions"]
  for i in [0:n] do
    let ctxRed ← hex "ctx_red" i
    let nf := MoussakaUnbound.derive k ctxRed
    let rreq ← hex "redeem_request" i
    errs := errs ++ checkEq s!"nf #{i}" nf (← hex "nf" i)
    errs := errs ++ checkEq s!"redeem_witness #{i}"
      (MoussakaUnbound.encodeRedeemWitness k ctxIss ctxRed rr s issuer) (← hex "redeem_witness" i)
    if rreq.length ≠ Moussaka.nfBytes + 12423 then errs := errs ++ [s!"redeem_request #{i}: bad length"]
    errs := errs ++ checkEq s!"redeem_request[0..24) #{i}" (rreq.take Moussaka.nfBytes) nf
  return errs

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
      -- The Client's `find_issuer` picks the KAT's issuer index (the witness above uses it).
      if Moussaka.findIssuer A t s ≠ some issuer then
        errs := errs ++ ["findIssuer: not the KAT's issuer index"]
      match Moussaka.redeemRequest zeroRedeemProver tok A ctxIss ctxRed cd [] with
      | .ok q =>
        errs := errs ++ checkEq "redeemRequest framing" (q.take Moussaka.nfBytes) (rreq.take Moussaka.nfBytes)
        if q.length ≠ Moussaka.redeemRequestBytes then errs := errs ++ ["redeemRequest: bad length"]
      | .error _ => errs := errs ++ ["redeemRequest rejected the honest token"]
      -- A token that no key of the set verifies is rejected.
      if (Moussaka.redeemRequest zeroRedeemProver ⟨tok.nf, tok.r, s.map (· ^^^ 1)⟩ A ctxIss ctxRed cd
          []) matches .ok _ then
        errs := errs ++ ["redeemRequest accepted a token that no key verifies"]
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

/-- PomFRIT's proof layout on `main`: dedicated label rows since `64fd1a4`. -/
def pomfritLayout : PomFRIT.Layout := .labelRows

def checkPomfritHeader (L : PomFRIT.Layout) (r : KatRecord) : Except String (List String) := do
  let mut errs : List String := []
  for (k, v) in [("signature_bytes", L.sigBytes), ("proof_bytes", L.proofBytes),
      ("refresher_bytes", PomFRIT.refresherBytes), ("vole_check_proof_offset", L.offVoleCheck),
      ("vole_check_proof_bytes", PomFRIT.voleCheckBytes), ("correction_offset", L.offCorrection),
      ("correction_bytes", PomFRIT.correctionBytes)] do
    if (← r.nat k) ≠ v then errs := errs ++ [s!"{k}: spec has {v}"]
  errs := errs ++ checkEq "pk_digest = SHAKE256(pk)" (shake256B (← r.bytes "pk") digestBytes)
    (← r.bytes "pk_digest")
  errs := errs ++ checkEq "sk" (← r.bytes "sk") (filled 0x60)
  return errs

def checkPomfrit (L : PomFRIT.Layout) (pk : UOVKey) (r : KatRecord) : Except String (List String) := do
  let seed ← r.bytes "seed"
  let msg ← r.bytes "msg"
  let t ← r.bytes "request"
  let s ← r.bytes "response"
  let chal1 ← r.bytes "chal1"
  let sig ← r.bytes "signature"
  let (_, refresher, rr) := PomFRIT.expandSeed pk.digest msg seed
  let h := L.hashToTarget pk.digest chal1 sig msg
  let mut errs : List String := []
  if sig.length ≠ L.sigBytes then errs := errs ++ ["signature: bad length"]
  errs := errs ++ checkEq "refresher" (L.sigRefresher sig) refresher
  errs := errs ++ checkEq "refresher_com" (L.sigRefresherCom sig)
    (PomFRIT.commitRefresher refresher)
  errs := errs ++ checkEq "request = H_T(...) ⊕ r" (xorBytes h rr) t
  if pk.eval s ≠ t then errs := errs ++ ["P(s) ≠ t"]
  if s.length ≠ uovN then errs := errs ++ ["response: bad length"]
  -- `verify` with the abstract verifier instantiated by the file's chal1 and a final check that the
  -- target it is handed is the Client's h = t ⊕ r.
  let V : PomFRIT.Verifier :=
    ⟨fun _ _ => some chal1, fun _ _ _ h' _ => decide (h' = xorBytes t rr)⟩
  if !L.verify V pk msg sig then errs := errs ++ ["verify (front end) rejected"]
  if L.verify V pk (msg ++ [0]) sig then errs := errs ++ ["verify accepted another message"]
  let sig' := sig.set (L.offCorrection + 3) ((sig.getD (L.offCorrection + 3) 0) ^^^ 1)
  if L.verify V pk msg sig' then errs := errs ++ ["verify accepted a modified d[0..M)"]
  let sig'' := sig.set (L.sigBytes - 1) ((sig.getD (L.sigBytes - 1) 0) ^^^ 1)
  if L.verify V pk msg sig'' then errs := errs ++ ["verify accepted a modified refresher"]
  return errs

/-- The executable model of pqov's signer on the key `pk` (oil matrix of `skSeed`) at `t`, against
the C++ response `s`. -/
def checkSigner (pk : UOVKey) (skSeed : Bytes) (label : String) (t s : Bytes) : IO Bool := do
  let t0 ← IO.monoMsNow
  let oa := (shake256B skSeed (16 + 74 * 45)).toArray
  let res ← IO.lazyPure fun _ => Pqov.deriveRefExec pk (Pqov.oilOfArray oa) skSeed t
  let ms := (← IO.monoMsNow) - t0
  match res with
  | none => report s!"{label}: pqov signer model ({ms} ms)" ["the model failed (255 attempts)"]
  | some (i, w) =>
    let mut errs : List String := []
    if w ≠ s then errs := errs ++ ["model preimage ≠ C++ derive_preimage response"]
    if pk.eval w ≠ t then errs := errs ++ ["P(model preimage) ≠ t"]
    report s!"{label}: pqov signer model = C++ derive_preimage (attempt {i.val}, {ms} ms)" errs

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
  let mous := parseKat (← IO.FS.readFile s!"{root}/tests/ihat/ihat_kat.txt")
  let mut pks : Std.HashMap String Verifier.UovPk := {}
  for r in mous do
    for sk in r.getAll "anchor_sk" do
      if !pks.contains sk then
        let some b := Hex.decodeByteArray? sk | throw (IO.userError s!"bad anchor_sk {sk}")
        pks := pks.insert sk (Verifier.UovPk.ofSecret b)
  IO.println s!"      UOV key generation: {pks.size + 3} keys ({(← IO.monoMsNow) - t0} ms)"
  -- Moussaka.
  if mous.size ≠ 3 then ok := false; IO.println s!"FAIL  ihat_kat.txt: {mous.size} records"
  for h : i in [0:mous.size] do
    let t1 ← IO.monoMsNow
    let errs ← IO.lazyPure fun _ =>
      runChecks (checkMoussaka keys pks ((mous[i].getAll "anchor_sk").length ≤ 3) mous[i])
    ok := (← report s!"ihat_kat.txt case {i} ({(← IO.monoMsNow) - t1} ms)" errs) && ok
  -- Unbound Moussaka tokens.
  let unb := parseKat (← IO.FS.readFile s!"{root}/tests/ihat/unbound_ihat_kat.txt")
  if unb.size = 0 then ok := false; IO.println "FAIL  unbound_ihat_kat.txt: empty"
  for h : i in [0:unb.size] do
    ok := (← report s!"unbound_ihat_kat.txt case {i}" (runChecks (checkMoussakaUnbound unb[i]))) && ok
  -- PomFRIT.
  let pom := parseKat (← IO.FS.readFile s!"{root}/tests/pomfrit/pomfrit_kat.txt")
  match pom[0]? with
  | none => ok := false; IO.println "FAIL  pomfrit_kat.txt: empty"
  | some hdr =>
    ok := (← report "pomfrit_kat.txt layout and key digest" (runChecks (checkPomfritHeader pomfritLayout hdr))) && ok
    let some test := keys["test"]? | throw (IO.userError "no key `test`")
    let dig ← IO.ofExcept (hdr.bytes "pk_digest")
    let pk := UOVKey.ofExpanded dig test
    if pom.size ≠ 4 then ok := false; IO.println s!"FAIL  pomfrit_kat.txt: {pom.size} records"
    for h : i in [1:pom.size] do
      ok := (← report s!"pomfrit_kat.txt case {i - 1}" (runChecks (checkPomfrit pomfritLayout pk pom[i]))) && ok
  -- pqov's signer model on the test key, at the Moussaka and PomFRIT targets.
  let some test := keys["test"]? | throw (IO.userError "no key `test`")
  let pkT := UOVKey.ofExpanded [] test
  let mut pairs : Array (String × Bytes × Bytes) := #[]
  for h : i in [0:mous.size] do
    if let (.ok req, .ok s) := (mous[i].bytes "issue_request", mous[i].bytes "issue_response") then
      pairs := pairs.push (s!"ihat_kat.txt case {i}", req.take uovM, s)
  for h : i in [1:pom.size] do
    if let (.ok t, .ok s) := (pom[i].bytes "request", pom[i].bytes "response") then
      pairs := pairs.push (s!"pomfrit_kat.txt case {i - 1}", t, s)
  if pairs.size ≠ 6 then ok := false; IO.println s!"FAIL  {pairs.size} signer targets, expected 6"
  for (label, t, s) in pairs do
    ok := (← checkSigner pkT (filled 0x60) label t s) && ok
  -- Ratatouille.
  let rata := parseKat (← IO.FS.readFile s!"{root}/tests/act/act_kat.txt")
  let rataResults := Ratatouille.Kats.checkFile keys rata
  if rataResults.length ≠ 3 then
    ok := false; IO.println s!"FAIL  act_kat.txt: {rataResults.length} cases"
  for (label, errs) in rataResults do
    ok := (← report label errs) && ok
  IO.println (if ok then "all spec known answers match" else "MISMATCHES")
  return if ok then 0 else 1

end VoleMole.Spec.Kats

def main (args : List String) : IO UInt32 := VoleMole.Spec.Kats.main args
