import VoleMole.Verifier.Relations
import VoleMole.Verifier.VectorFile

/-!
# Full verification of the KAT proofs

Runs `Verifier.verify` on every proof in `tests/ihat/ihat_kat.txt` (issuance and
redemption requests), `tests/act/act_kat.txt` (issuance and spend requests) and
`tests/pomfrit/pomfrit_kat.txt` (blind signatures, with PomFRIT's refresher check), building each
statement from the KAT fields alone: the UOV public keys are generated in Lean from the compact
secret keys (`Keygen.compressedPk`, pqov's key generation, then `expand_pk`) or, for PomFRIT, expanded
from the compressed key in the KAT file. When present, `lean/vectors/verifier_keys.txt` (compressed
public keys dumped by `tests/voleith/dump_verifier_vectors.cpp`) and the expanded `test` key of
`uov_keys.txt` are compared with the generated keys; neither is needed. Every proof must be accepted. For the first proof of each relation, a byte flipped in each
proof field, and a changed instance, must be rejected. The transcripts of the proofs that also
appear in `verifier_kat.txt` are compared with the dumped `chal2` and `qs_check`.

`layouts` says which relations use the dedicated-label-row layout (`Params.labelRows`): on `main`
(since `64fd1a4`) PomFRIT only; `Layouts.all` for the KAT files of branch `voleith-label-rows`.
-/

namespace VoleMole.Verifier.Kats

open VoleMole.Verifier

abbrev Lines := Array (String × String)

def readLines (path : String) : IO Lines := do
  let mut out : Lines := #[]
  for line in (← IO.FS.readFile path).splitOn "\n" do
    if line.isEmpty || line.startsWith "#" then continue
    match line.splitOn " " with
    | [k] => out := out.push (k, "")
    | k :: v :: _ => out := out.push (k, v)
    | [] => pure ()
  return out

def unhex (s : String) : ByteArray := (Vectors.unhex s).getD ByteArray.empty

/-- Split at each occurrence of `key`. -/
def records (ls : Lines) (key : String) : Array Lines := Id.run do
  let mut out : Array Lines := #[]
  for (k, v) in ls do
    if k == key then out := out.push #[]
    if h : 0 < out.size then
      out := out.set (out.size - 1) (out[out.size - 1].push (k, v))
  return out

def get (r : Lines) (k : String) (n : Nat := 0) : String :=
  ((r.filter (·.1 == k))[n]?.map (·.2)).getD ""

def getAll (r : Lines) (k : String) : Array String := (r.filter (·.1 == k)).map (·.2)

instance : Hashable ByteArray := ⟨fun b => hash b.toList⟩

structure Ctx where
  T : CrtTables
  /-- Compact secret key (hex) ↦ compressed public key (generated in Lean). -/
  cpks : Std.HashMap String ByteArray
  /-- Proof (hex) ↦ dumped `chal2`, `qs_check`. -/
  dumped : Std.HashMap ByteArray (ByteArray × ByteArray)
  /-- Only run the checks whose label starts with this. -/
  filter : String := ""
  /-- Which relations use dedicated label rows (`Params.labelRows`). -/
  layouts : Layouts := Layouts.main
  /-- Number of valid proofs verified, and of mutations rejected. -/
  accepted : IO.Ref Nat
  rejected : IO.Ref Nat

def Ctx.pk (c : Ctx) (sk : String) : Except String UovPk :=
  match c.cpks[sk]? with
  | some cpk => .ok (UovPk.ofCompressed cpk)
  | none => .error s!"no compressed public key for {sk}"

/-- Verify one proof; report failures. `expect` is the expected verdict. -/
def run (c : Ctx) (label : String) (expect : Bool) (proof : ByteArray) (t : Unit → Transcript) :
    IO Bool := do
  if !label.startsWith c.filter then return true
  let t0 ← IO.monoMsNow
  let tr ← IO.lazyPure t
  let t1 ← IO.monoMsNow
  let mut ok := tr.accept == expect
  if ok then (if expect then c.accepted else c.rejected).modify (· + 1)
  if !ok then
    IO.eprintln s!"FAIL {label}: accept = {tr.accept}, expected {expect} {tr.error}"
  if expect then
    if let some (c2, qc) := c.dumped[proof]? then
      if tr.chal2 != c2 || tr.qsCheck != qc then
        IO.eprintln s!"FAIL {label}: transcript differs from the dump (chal2 {tr.chal2 == c2})"
        ok := false
    IO.println s!"  {label}: {if tr.accept then "accepted" else "REJECTED"} ({t1 - t0} ms)"
  else
    IO.println s!"  {label}: {if tr.accept then "ACCEPTED" else "rejected"} ({t1 - t0} ms)"
  (← IO.getStdout).flush
  return ok

/-- Flip byte `off` of `b`. -/
def flip (b : ByteArray) (off : Nat) : ByteArray := b.set! off (b.get! off ^^^ 0x01)

/-- Mutations of a proof: a byte flipped in the middle of each field. -/
def mutations (p : Params) : List (String × Nat) :=
  p.fieldSizes.filterMap fun (k, _) => (p.field? k).map fun (off, n) => (k, off + n / 2)

def moussaka (c : Ctx) (path : String) : IO Bool := do
  let mut ok := true
  let recs := records (← readLines path) "issue_seed"
  for i in [0:recs.size] do
    let r := recs[i]!
    let ctxIss := unhex (get r "ctx_iss")
    let ctxRed := unhex (get r "ctx_red")
    let cd := unhex (get r "challenge_digest")
    let req := unhex (get r "issue_request")
    let t := req.extract 0 45
    let proof := req.extract 45 req.size
    ok := (← run c s!"moussaka {i} issue" true proof fun _ =>
      verify Hashes.shake c.T (moussakaIssue t ctxIss c.layouts.moussaka) proof) && ok
    if i == 0 then
      for (k, off) in mutations (moussakaIssue t ctxIss c.layouts.moussaka).params do
        ok := (← run c s!"moussaka {i} issue, mutated {k}" false proof fun _ =>
          verify Hashes.shake c.T (moussakaIssue t ctxIss c.layouts.moussaka) (flip proof off)) && ok
      ok := (← run c s!"moussaka {i} issue, wrong ctx_iss" false proof fun _ =>
        verify Hashes.shake c.T (moussakaIssue t (flip ctxIss 0) c.layouts.moussaka) proof) && ok
    let anchors ← IO.ofExcept ((getAll r "anchor_sk").toList.mapM c.pk)
    let rreq := unhex (get r "redeem_request")
    let nf := rreq.extract 0 24
    let rproof := rreq.extract 24 rreq.size
    let st := moussakaRedeem anchors nf ctxIss ctxRed cd c.layouts.moussaka
    ok := (← run c s!"moussaka {i} redeem ({anchors.length} anchors)" true rproof fun _ =>
      verify Hashes.shake c.T st rproof) && ok
    if i == 0 then
      for (k, off) in mutations st.params do
        ok := (← run c s!"moussaka {i} redeem, mutated {k}" false rproof fun _ =>
          verify Hashes.shake c.T st (flip rproof off)) && ok
      ok := (← run c s!"moussaka {i} redeem, wrong challenge_digest" false rproof fun _ =>
        verify Hashes.shake c.T (moussakaRedeem anchors nf ctxIss ctxRed (flip cd 0) c.layouts.moussaka) rproof) && ok
  return ok

def ratatouille (c : Ctx) (path : String) : IO Bool := do
  let mut ok := true
  let recs := records (← readLines path) "issue_seed"
  for i in [0:recs.size] do
    let r := recs[i]!
    let ctxIss := unhex (get r "ctx_iss")
    let tInit := (get r "t_init").toNat!
    let pk ← IO.ofExcept (c.pk (get r "issuer_sk"))
    let req := unhex (get r "issue_request")
    let cc := req.extract 0 32
    let proof := req.extract 32 req.size
    ok := (← run c s!"ratatouille {i} issue" true proof fun _ =>
      verify Hashes.shake c.T (ratatouilleIssue cc tInit ctxIss c.layouts.ratatouille) proof) && ok
    if i == 0 then
      for (k, off) in mutations (ratatouilleIssue cc tInit ctxIss c.layouts.ratatouille).params do
        ok := (← run c s!"ratatouille {i} issue, mutated {k}" false proof fun _ =>
          verify Hashes.shake c.T (ratatouilleIssue cc tInit ctxIss c.layouts.ratatouille) (flip proof off)) && ok
      ok := (← run c s!"ratatouille {i} issue, wrong t_init" false proof fun _ =>
        verify Hashes.shake c.T (ratatouilleIssue cc (tInit + 1) ctxIss c.layouts.ratatouille) proof) && ok
    let spends := getAll r "spend_request"
    for j in [0:spends.size] do
      let sreq := unhex spends[j]!
      let nf := sreq.extract 0 24
      let d := (sreq.extract 24 32).toList.foldr (fun b acc => acc * 256 + b.toNat) 0
      let cNext := sreq.extract 32 64
      let sproof := sreq.extract 64 sreq.size
      let st := ratatouilleSpend pk nf d cNext ctxIss c.layouts.ratatouille
      ok := (← run c s!"ratatouille {i} spend {j}" true sproof fun _ => verify Hashes.shake c.T st sproof) && ok
      if i == 0 && j == 0 then
        for (k, off) in mutations st.params do
          ok := (← run c s!"ratatouille {i} spend {j}, mutated {k}" false sproof fun _ =>
            verify Hashes.shake c.T st (flip sproof off)) && ok
        ok := (← run c s!"ratatouille {i} spend {j}, wrong d" false sproof fun _ =>
          verify Hashes.shake c.T (ratatouilleSpend pk nf (d + 1) cNext ctxIss c.layouts.ratatouille) sproof) && ok
  return ok

def pomfrit (c : Ctx) (path : String) : IO Bool := do
  let ls ← readLines path
  let pk := UovPk.ofCompressed (unhex (get ls "pk"))
  let mut ok := (← Vectors.check "pomfrit pk digest" (pk.digest == unhex (get ls "pk_digest")))
  let recs := records ls "seed"
  for i in [0:recs.size] do
    let r := recs[i]!
    let sig := unhex (get r "signature")
    let msg := unhex (get r "msg")
    let proof := sig.extract 0 (pomfritParams c.layouts.pomfrit).proofBytes
    ok := (← run c s!"pomfrit {i}" true proof fun _ => pomfritVerify Hashes.shake c.T pk sig msg c.layouts.pomfrit) && ok
    if i == 0 then
      for (k, off) in mutations (pomfritParams c.layouts.pomfrit) do
        ok := (← run c s!"pomfrit {i}, mutated {k}" false proof fun _ =>
          pomfritVerify Hashes.shake c.T pk (flip sig off) msg c.layouts.pomfrit) && ok
      ok := (← run c s!"pomfrit {i}, mutated refresher" false proof fun _ =>
        pomfritVerify Hashes.shake c.T pk (flip sig (sig.size - 1)) msg c.layouts.pomfrit) && ok
      ok := (← run c s!"pomfrit {i}, wrong msg" false proof fun _ =>
        pomfritVerify Hashes.shake c.T pk sig (msg.push 0) c.layouts.pomfrit) && ok
  return ok

/-- Run everything; `dir` is the vector directory, `tests` the repository's `tests/`. -/
def main (T : CrtTables) (dumpedRecs : Array Vectors.Record) (dir tests filter : String)
    (layouts : Layouts) : IO Bool := do
  -- UOV keys: generated from every compact secret key in the KAT files.
  let mousPath := s!"{tests}/ihat/ihat_kat.txt"
  let rataPath := s!"{tests}/act/act_kat.txt"
  let sks := (getAll (← readLines mousPath) "anchor_sk") ++ (getAll (← readLines rataPath) "issuer_sk")
  let t0 ← IO.monoMsNow
  let mut cpks : Std.HashMap String ByteArray := {}
  for sk in sks do
    if !cpks.contains sk then cpks := cpks.insert sk (Keygen.compressedPk (unhex sk))
  let t1 ← IO.monoMsNow
  IO.println s!"UOV key generation: {cpks.size} keys ({t1 - t0} ms)"
  let mut ok := true
  -- Optional cross-checks against the C++ keys.
  if ← System.FilePath.pathExists s!"{dir}/verifier_keys.txt" then
    let mut n := 0
    let mut bad := 0
    for line in (← IO.FS.readFile s!"{dir}/verifier_keys.txt").splitOn "\n" do
      if let ["key", sk, cpk] := line.splitOn " " then
        n := n + 1
        let ours := match cpks[sk]? with
          | some k => k
          | none => Keygen.compressedPk (unhex sk)
        if ours != unhex cpk then bad := bad + 1
    IO.println s!"  generated keys = C++ compressed keys (verifier_keys.txt): {n - bad} of {n}"
    ok := (← Vectors.check s!"pqov key generation = C++ compressed keys ({n} keys of verifier_keys.txt)"
      (n > 0 && bad == 0)) && ok
  else IO.println "  (no verifier_keys.txt: generated keys not compared with the C++)"
  let mut dumped : Std.HashMap ByteArray (ByteArray × ByteArray) := {}
  for r in dumpedRecs do
    if r.group == "kat" then
      dumped := dumped.insert (r.bytes "proof") (r.bytes "chal2", r.bytes "qs_check")
  let c : Ctx := { T, cpks, dumped, filter, layouts, accepted := ← IO.mkRef 0, rejected := ← IO.mkRef 0 }
  -- The expansion of the `test` key agrees with the C++ expanded key of `uov_keys.txt`.
  if ← System.FilePath.pathExists s!"{dir}/uov_keys.txt" then
    let testSk := "606162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f"
    let mut expTest : ByteArray := ByteArray.empty
    for line in (← IO.FS.readFile s!"{dir}/uov_keys.txt").splitOn "\n" do
      match line.splitOn " " with
      | ["key", "test", hex] => expTest := unhex hex
      | _ => pure ()
    ok := (← Vectors.check "UOV key generation + expand_pk (test key) = C++ expanded key"
      (match c.pk testSk with | .ok pk => pk.expanded == expTest | .error _ => false)) && ok
    IO.println "  expanded `test` key compared with uov_keys.txt"
  let ok1 ← moussaka c mousPath
  let ok2 ← ratatouille c rataPath
  let ok3 ← pomfrit c s!"{tests}/pomfrit/pomfrit_kat.txt"
  IO.println s!"KAT proofs: {← c.accepted.get} accepted, {← c.rejected.get} mutations rejected, \
    {if ok1 && ok2 && ok3 then "ok" else "FAILED"}"
  return ok && ok1 && ok2 && ok3

end VoleMole.Verifier.Kats
