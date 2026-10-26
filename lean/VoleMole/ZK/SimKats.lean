import VoleMole.ZK.Sim
import VoleMole.Verifier.ProverKats

/-!
# Smoke test of the simulator and the ideal-tape prover (`lake exe zk_sim`, root `SimMain.lean`)

For every proof of the three KAT files (the statements, witnesses and prover randomness of
`ProverKats.lean`), with SHAKE128 as the hash record:

* **tape of the real run**: `proveIdeal Hs (tapeOf Hs … rho) = prove Hs … rho` byte for byte (the
  statement of `ZK/TapeOf.lean`);
* **simulator**: with pseudorandom coins, `simulateRO` returns a proof that the verifier accepts with
  the programmed hashes, and rejects with the unprogrammed ones (it is not a real proof);
* **ideal tape**: the ideal-tape prover on a pseudorandom tape returns a proof that the verifier
  accepts once `H₂³` is programmed at its grinding points (`programPoints`), as the real prover's
  run on the ideal tape should (not for PomFRIT: with delayed instance binding the instance
  depends on `chal1`, so a fixed witness satisfies only the statement built from its own run).

All coins are SHAKE128 outputs of labels (reproducible). Usage:
`lake exe zk_sim [TESTS_DIR [main|labelrows [FILTER]]]` (default `../tests`, `main`).
-/

namespace VoleMole.ZK.SimKats

open VoleMole.Verifier VoleMole.Verifier.Kats VoleMole.ZK.Sim

/-- `n` pseudorandom bytes from a label. -/
def coins (label : String) (n : Nat) : Bytes n := blk n (Spec.SHAKE.shake128 label.toUTF8 n)

/-- A pseudorandom shared tape. -/
def sharedOf (label : String) : Shared :=
  (coins s!"{label}/iv_pre" 16, fun c => coins s!"{label}/grind/{c.val}" 16,
   fun i => coins s!"{label}/com/{i.val}" 32, fun k => coins s!"{label}/seed/{k.val}" 16)

/-- Pseudorandom simulator coins. -/
def simCoinsOf (p : Params) (label : String) : SimCoins p :=
  (sharedOf label, coins s!"{label}/c" _, coins s!"{label}/cmult" _, coins s!"{label}/ut" _,
   coins s!"{label}/d" _, coins s!"{label}/at" _)

/-- A pseudorandom ideal tape. -/
def idealTapeOf (p : Params) (label : String) : IdealTape p :=
  (sharedOf label,
   (coins s!"{label}/u0w" _, coins s!"{label}/theta" _, fun i => coins s!"{label}/u/{i.val}" _,
    fun i => coins s!"{label}/low/{i.val}" _, fun i => coins s!"{label}/rest/{i.val}" _,
    coins s!"{label}/hi" _, fun e => coins s!"{label}/sib/{e.val}" 4))

structure Ctx where
  T : CrtTables
  pc : ProverKats.Ctx
  filter : String
  passed : IO.Ref Nat

/-- The three checks for one statement, witness and prover randomness; `real` computes the real
prover's output (`Prover.prove`, or PomFRIT's two steps; only run if `label` passes the filter). -/
def checkRun (c : Ctx) (label : String) (st : Statement) (w rho : ByteArray)
    (real : Unit → Except String ByteArray) (prefixBytes : Nat := st.params.witnessBytes) : IO Bool := do
  if !label.startsWith c.filter then return true
  let Hs := Hashes.shake
  let p := st.params
  let t0 ← IO.monoMsNow
  let mut ok := true
  -- The ideal-tape prover at the run's own tape.
  let ideal ← IO.lazyPure fun _ => proveIdeal Hs c.T st w (tapeOf Hs c.T st w rho prefixBytes)
  let tapeOk := match real (), ideal with
    | .ok a, .ok b => a == b
    | _, _ => false
  if !tapeOk then
    ok := false
    IO.eprintln s!"FAIL {label}: proveIdeal (tapeOf …) ≠ prove"
  -- The simulator, with the programmed oracle.
  let simOk ← IO.lazyPure fun _ => match simulateRO Hs c.T st (simCoinsOf p s!"{label} sim") with
    | .ok (proof, Hs') =>
      ((verify Hs' c.T st proof).accept, (verify Hs c.T st proof).accept)
    | .error _ => (false, true)
  if !simOk.1 then
    ok := false
    IO.eprintln s!"FAIL {label}: the verifier rejects the simulated proof (programmed oracle)"
  if simOk.2 then
    ok := false
    IO.eprintln s!"FAIL {label}: the verifier accepts the simulated proof without programming"
  -- The ideal-tape prover on a pseudorandom tape, with `H₂³` programmed at its grinding points.
  -- (Not for delayed instance binding: there the instance, and so whether `w` satisfies the
  -- constraints, depends on `chal1`, which a fresh tape changes.)
  let t := idealTapeOf p s!"{label} ideal"
  let idealOk ← IO.lazyPure fun _ => if st.delayed then true else
    match proveIdeal Hs c.T st w t with
    | .ok proof =>
      let ctr := ((firstHit t.1.2.1).map (·.1)).getD 0
      (verify (program Hs (programPoints Hs c.T st proof t.1.2.1 ctr)) c.T st proof).accept
    | .error _ => false
  if !idealOk then
    ok := false
    IO.eprintln s!"FAIL {label}: the verifier rejects the ideal-tape proof (programmed oracle)"
  let t1 ← IO.monoMsNow
  if ok then c.passed.modify (· + 1)
  IO.println s!"  {label}: tapeOf {if tapeOk then "= prove" else "DIFFERS"}, simulated proof \
    {if simOk.1 then "accepted" else "REJECTED"} (unprogrammed: \
    {if simOk.2 then "ACCEPTED" else "rejected"}), ideal-tape proof \
    {if st.delayed then "not run" else if idealOk then "accepted" else "REJECTED"} \
    ({t1 - t0} ms)"
  (← IO.getStdout).flush
  return ok

def moussaka (c : Ctx) (path : String) : IO Bool := do
  let mut ok := true
  let recs := records (← readLines path) "issue_seed"
  for i in [0:recs.size] do
    let r := recs[i]!
    let ctxIss := unhex (get r "ctx_iss")
    let ctxRed := unhex (get r "ctx_red")
    let cd := unhex (get r "challenge_digest")
    let req := unhex (get r "issue_request")
    let st := moussakaIssue (req.extract 0 45) ctxIss c.pc.layouts.moussaka
    let w := unhex (get r "issue_witness")
    let rho := toBA (Spec.Moussaka.expandIssueSeed (toL (unhex (get r "issue_seed")))).2.2
    ok := (← checkRun c s!"moussaka {i} issue" st w rho
      fun _ => Prover.prove Hashes.shake c.T st w rho) && ok
    let anchors ← IO.ofExcept ((getAll r "anchor_sk").toList.mapM c.pc.pk)
    let rreq := unhex (get r "redeem_request")
    let rst := moussakaRedeem anchors (rreq.extract 0 24) ctxIss ctxRed cd c.pc.layouts.moussaka
    let rw := unhex (get r "redeem_witness")
    let rrho := toBA (Spec.Moussaka.expandRedeemSeed (toL (unhex (get r "redeem_seed"))))
    ok := (← checkRun c s!"moussaka {i} redeem" rst rw rrho
      fun _ => Prover.prove Hashes.shake c.T rst rw rrho) && ok
  return ok

def ratatouille (c : Ctx) (path : String) : IO Bool := do
  let mut ok := true
  let recs := records (← readLines path) "issue_seed"
  let rho (dst : List UInt8) (seed : ByteArray) : ByteArray :=
    ⟨(Spec.Ratatouille.expandSeed dst (Vector.ofFn fun k => seed.get! k.1)).2.2.toArray⟩
  for i in [0:recs.size] do
    let r := recs[i]!
    let ctxIss := unhex (get r "ctx_iss")
    let tInit := (get r "t_init").toNat!
    let pk ← IO.ofExcept (c.pc.pk (get r "issuer_sk"))
    let req := unhex (get r "issue_request")
    let st := ratatouilleIssue (req.extract 0 32) tInit ctxIss c.pc.layouts.ratatouille
    let w := unhex (get r "issue_witness")
    let irho := rho Spec.Ratatouille.issueSeedDst (unhex (get r "issue_seed"))
    ok := (← checkRun c s!"ratatouille {i} issue" st w irho
      fun _ => Prover.prove Hashes.shake c.T st w irho) && ok
    let spends := getAll r "spend_request"
    let sws := getAll r "spend_witness"
    let sseeds := getAll r "spend_seed"
    for j in [0:spends.size] do
      let sreq := unhex spends[j]!
      let d := (sreq.extract 24 32).toList.foldr (fun b acc => acc * 256 + b.toNat) 0
      let sst := ratatouilleSpend pk (sreq.extract 0 24) d (sreq.extract 32 64) ctxIss
        c.pc.layouts.ratatouille
      let sw := unhex sws[j]!
      let srho := rho Spec.Ratatouille.spendSeedDst (unhex sseeds[j]!)
      ok := (← checkRun c s!"ratatouille {i} spend {j}" sst sw srho
        fun _ => Prover.prove Hashes.shake c.T sst sw srho) && ok
  return ok

/-- PomFRIT: the statement is built from step 1's output, the real proof is the two steps'. -/
def pomfrit (c : Ctx) (path : String) : IO Bool := do
  let ls ← readLines path
  let pk := UovPk.ofCompressed (unhex (get ls "pk"))
  let mut ok := true
  let recs := records ls "seed"
  for i in [0:recs.size] do
    if !s!"pomfrit {i}".startsWith c.filter then continue
    let r := recs[i]!
    let msg := unhex (get r "msg")
    let seed := unhex (get r "seed")
    let s := unhex (get r "response")
    let p := pomfritParams c.pc.layouts.pomfrit
    let (rho, refresher, rr) := Spec.PomFRIT.expandSeed (toL pk.digest) (toL msg) (toL seed)
    let com := toBA (Spec.PomFRIT.commitRefresher refresher)
    let dst := toBA (Spec.makeDst "pomf" 0 'p' '0')
    let pend := Prover.voleGen Hashes.shake c.T p (mu Hashes.shake none dst) (toBA rr) (toBA rho)
      com
    let st := pomfritRedeem pk (pend.proof ++ com ++ toBA refresher) msg c.pc.layouts.pomfrit
    ok := (← checkRun c s!"pomfrit {i}" st (toBA rr ++ s) (toBA rho)
      (fun _ => Prover.proveCommit Hashes.shake st s pend) rr.length) && ok
  return ok

def main (args : List String) : IO UInt32 := do
  let tests := args.headD "../tests"
  let layouts := Layouts.ofArg (args.getD 1 "")
  let filter := args.getD 2 ""
  let mousPath := s!"{tests}/moussaka/moussaka_kat.txt"
  let rataPath := s!"{tests}/ratatouille/ratatouille_kat.txt"
  let sks :=
    (getAll (← readLines mousPath) "anchor_sk") ++ (getAll (← readLines rataPath) "issuer_sk")
  let mut cpks : Std.HashMap String ByteArray := {}
  for sk in sks do
    if !cpks.contains sk then cpks := cpks.insert sk (Keygen.compressedPk (unhex sk))
  IO.println s!"Proof layout: {layouts.describe}"
  let pc : ProverKats.Ctx :=
    { T := CrtGen.tables, cpks := cpks, layouts := layouts, filter := filter,
      reproduced := ← IO.mkRef 0, verified := ← IO.mkRef 0 }
  let c : Ctx := { T := CrtGen.tables, pc := pc, filter := filter, passed := ← IO.mkRef 0 }
  let t0 ← IO.monoMsNow
  let ok1 ← moussaka c mousPath
  let ok2 ← ratatouille c rataPath
  let ok3 ← pomfrit c s!"{tests}/pomfrit/pomfrit_kat.txt"
  let t1 ← IO.monoMsNow
  let ok := ok1 && ok2 && ok3
  IO.println s!"ZK simulator: {← c.passed.get} runs passed (tapeOf, simulator, ideal tape), \
    {if ok then "ok" else "FAILED"} ({t1 - t0} ms)"
  return if ok then 0 else 1

end VoleMole.ZK.SimKats
