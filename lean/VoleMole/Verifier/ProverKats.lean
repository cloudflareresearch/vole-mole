import VoleMole.Verifier.Prover
import VoleMole.Verifier.Kats
import VoleMole.Spec.Ratatouille

/-!
# The Lean prover against the KAT proofs (`lake exe prover_vectors`, root `ProverMain.lean`)

For every proof in `tests/moussaka/moussaka_kat.txt`, `tests/ratatouille/ratatouille_kat.txt` and
`tests/pomfrit/pomfrit_kat.txt`, run `Prover.prove` (`Prover.voleGen` and `Prover.proveCommit` for
PomFRIT) on the KAT's witness and statement, with the prover randomness `rho` derived from the KAT
seed as the C++ does (`Spec.Moussaka.expandIssueSeed`/`expandRedeemSeed`,
`Spec.Ratatouille.expandSeed`, `Spec.PomFRIT.expandSeed`), and require the C++'s proof byte for
byte. Every Lean proof is also verified (`Verifier.verify`, must accept).

The witnesses are the KATs' `issue_witness`, `redeem_witness`, `spend_witness`; PomFRIT's is
`r ‖ s` with `r` from the seed and `s` the Signer's `response`. PomFRIT is proved in two steps as in
`src/pomfrit/pomfrit.cpp`: step 1 with `r`, `mu₁ = H(DST ‖ 12)` and the binder `refresher_com`; the
statement (`pomfritRedeem`, whose instance `h = hash_to_target(…)` reads `ũ` and `d[0..45)` from
step 1's output) is built after it; step 2 with `s` and the binder `refresher`.

Every Lean proof is also checked against the two facts that `Bridge/Prover.lean`'s completeness
theorem assumes (`checkCorrelation`): the opening reconstructs the prover's leaf keys and
commitments, and the verifier's CRT-lifted rows and masks at the proof's `Δ` are `v + u·Δ'`.

Completeness smoke test (`random`, `randomUov`): statements and witnesses of all five relations
built from fresh pseudorandom seeds and contexts, the way the protocols build them
(`Spec.Moussaka.com`/`encodeIssueWitness`/`encodeRedeemWitness`, `Spec.Ratatouille.com`/
`encodeIssueWitness`/`encodeSpendWitness`, PomFRIT's two steps), with the issuers' UOV preimages
from a test-only sampler (`sample`, below), proved with random `rho` and verified (PomFRIT also
through `pomfritVerify`). A changed witness bit, or a wrong Signer response, must make the prover
fail (the constraint check of `Prover.qsProve`).

With `labelrows`, all statements use the dedicated-label-row layout, for the KAT files of branch
`voleith-label-rows`.

Usage: `lake exe prover_vectors [TESTS_DIR [main|labelrows [FILTER]]]` (default `../tests`, `main`;
with a filter, only the runs whose label starts with it).
-/

namespace VoleMole.Verifier.ProverKats

open VoleMole.Verifier VoleMole.Verifier.Kats

structure Ctx where
  T : CrtTables
  cpks : Std.HashMap String ByteArray
  layouts : Layouts
  filter : String
  reproduced : IO.Ref Nat
  verified : IO.Ref Nat

def Ctx.pk (c : Ctx) (sk : String) : Except String UovPk :=
  match c.cpks[sk]? with
  | some cpk => .ok (UovPk.ofCompressed cpk)
  | none => .error s!"no compressed public key for {sk}"

/-- Run the prover; compare with `expected` (if given) and verify the output. -/
def run (c : Ctx) (label : String) (st : Statement) (expected : Option ByteArray)
    (prove : Unit → Except String ByteArray) : IO Bool := do
  if !label.startsWith c.filter then return true
  let t0 ← IO.monoMsNow
  let out ← IO.lazyPure prove
  let t1 ← IO.monoMsNow
  match out with
  | .error e =>
    IO.eprintln s!"FAIL {label}: prover error: {e}"
    return false
  | .ok pf =>
    let mut ok := true
    let mut msg := ""
    if let some exp := expected then
      if pf == exp then
        c.reproduced.modify (· + 1)
        msg := "= C++"
      else
        ok := false
        let pr : Proof := { params := st.params, bytes := pf }
        let pe : Proof := { params := st.params, bytes := exp }
        let diff := st.params.fieldSizes.filterMap fun (k, _) =>
          if pr.field k != pe.field k then some k else none
        IO.eprintln s!"FAIL {label}: proof differs from the C++ (fields {diff})"
        msg := "DIFFERENT"
    let t2 ← IO.monoMsNow
    let tr ← IO.lazyPure fun _ => verify Hashes.shake c.T st pf
    let t3 ← IO.monoMsNow
    if tr.accept then c.verified.modify (· + 1)
    else
      ok := false
      IO.eprintln s!"FAIL {label}: the verifier rejects the Lean proof {tr.error}"
    IO.println s!"  {label}: {msg} {if tr.accept then "accepted" else "REJECTED"} \
      (prove {t1 - t0} ms, verify {t3 - t2} ms)"
    (← IO.getStdout).flush
    return ok

/-- The VOLE correlation of a Lean proof, recomputed by the verifier at the proof's `Δ`: the
opening reconstructs the prover's leaf keys off the hidden leaves and its commitments
(`BAVC.reconstruct`), the lifted rows are `v_r + u_r Δ'` (proved: `Bridge.prover_row`) and the
masks are `ṽ_mask[m] + u_mask[m] Δ'` (the CRT VOLE's correctness, assumed by
`Bridge.verify_prove`). -/
def checkCorrelation (T : CrtTables) (s : Prover.Pending) (proof : ByteArray) :
    Except String Unit := do
  let p := s.params
  let pf : Proof := { params := p, bytes := proof }
  let some leaves := BAVC.reconstruct s.iv pf.opening pf.delta | throw "opening rejected"
  if leaves.coms != s.leaves.coms then throw "commitments differ"
  for i in [0:BAVC.tau] do
    for j in [0:2 ^ BAVC.kOf i] do
      if j != BAVC.deltaIndex pf.delta i && leafKey leaves i j != leafKey s.leaves i j then
        throw "leaf keys differ"
  let crt := crtReconstruct Hashes.shake pf T s.iv (convertToVole pf s.iv leaves)
  let dL := crt.deltaLifted.toGF
  for r in [0:p.correctionRows] do
    if crt.rows[r]!.toGF != s.vRows[r]!.toGF + (if wbit s.u r then 1 else 0) * dL then
      throw s!"row {r}: q ≠ v + u Δ"
  for m in [0:p.nMask] do
    if crt.qMask[m]!.toGF != s.vMask[m]!.toGF + s.uMask[m]!.toGF * dL then
      throw s!"mask {m}: q ≠ v + u Δ"

/-- `Prover.prove`, followed by `checkCorrelation`. -/
def proveChecked (T : CrtTables) (st : Statement) (w rho : ByteArray) :
    Except String ByteArray := do
  let s := Prover.voleGen Hashes.shake T st.params (st.mu1 Hashes.shake) w rho st.binder1
  let pf ← Prover.proveCommit Hashes.shake st ByteArray.empty s
  checkCorrelation T s pf
  return pf

/-- The prover must fail on a witness with bit `j` flipped. -/
def runBad (c : Ctx) (label : String) (prove : Unit → Except String ByteArray) : IO Bool := do
  if !label.startsWith c.filter then return true
  match ← IO.lazyPure prove with
  | .error _ => IO.println s!"  {label}: prover refuses"; return true
  | .ok _ =>
    IO.eprintln s!"FAIL {label}: the prover accepted a non-satisfying witness"; return false

def flipBit (b : ByteArray) (j : Nat) : ByteArray :=
  b.set! (j / 8) (b.get! (j / 8) ^^^ ((1 : UInt8) <<< (j % 8).toUInt8))

/-- 16 or 32 pseudorandom bytes from a label (SHAKE128, so that runs are reproducible). -/
def rnd (label : String) (n : Nat := 16) : ByteArray := Spec.SHAKE.shake128 label.toUTF8 n

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
    let st := moussakaIssue t ctxIss c.layouts.moussaka
    let w := unhex (get r "issue_witness")
    let rho := toBA (Spec.Moussaka.expandIssueSeed (toL (unhex (get r "issue_seed")))).2.2
    ok := (← run c s!"moussaka {i} issue" st (some (req.extract 45 req.size)) fun _ =>
      proveChecked c.T st w rho) && ok
    if i == 0 then
      ok := (← run c s!"moussaka {i} issue, random rho" st none fun _ =>
        proveChecked c.T st w (rnd s!"moussaka {i} issue rho")) && ok
      ok := (← runBad c s!"moussaka {i} issue, witness bit 1000 flipped" fun _ =>
        Prover.prove Hashes.shake c.T st (flipBit w 1000) rho) && ok
    let anchors ← IO.ofExcept ((getAll r "anchor_sk").toList.mapM c.pk)
    let rreq := unhex (get r "redeem_request")
    let nf := rreq.extract 0 24
    let rst := moussakaRedeem anchors nf ctxIss ctxRed cd c.layouts.moussaka
    let rw := unhex (get r "redeem_witness")
    let rrho := toBA (Spec.Moussaka.expandRedeemSeed (toL (unhex (get r "redeem_seed"))))
    ok := (← run c s!"moussaka {i} redeem ({anchors.length} anchors)" rst
      (some (rreq.extract 24 rreq.size)) fun _ => proveChecked c.T rst rw rrho) && ok
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
    let pk ← IO.ofExcept (c.pk (get r "issuer_sk"))
    let req := unhex (get r "issue_request")
    let cc := req.extract 0 32
    let st := ratatouilleIssue cc tInit ctxIss c.layouts.ratatouille
    let w := unhex (get r "issue_witness")
    ok := (← run c s!"ratatouille {i} issue" st (some (req.extract 32 req.size)) fun _ =>
      proveChecked c.T st w (rho Spec.Ratatouille.issueSeedDst (unhex (get r "issue_seed")))) && ok
    let spends := getAll r "spend_request"
    let sws := getAll r "spend_witness"
    let sseeds := getAll r "spend_seed"
    for j in [0:spends.size] do
      let sreq := unhex spends[j]!
      let nf := sreq.extract 0 24
      let d := (sreq.extract 24 32).toList.foldr (fun b acc => acc * 256 + b.toNat) 0
      let cNext := sreq.extract 32 64
      let sst := ratatouilleSpend pk nf d cNext ctxIss c.layouts.ratatouille
      ok := (← run c s!"ratatouille {i} spend {j}" sst (some (sreq.extract 64 sreq.size)) fun _ =>
        proveChecked c.T sst (unhex sws[j]!) (rho Spec.Ratatouille.spendSeedDst (unhex sseeds[j]!)))
        && ok
  return ok

/-- PomFRIT's two steps (`issue_request_with_seed`, `finalize_issue`). -/
def pomfritProve (c : Ctx) (pk : UovPk) (msg seed s rhoOverride : ByteArray) :
    Except String ByteArray :=
  let p := pomfritParams c.layouts.pomfrit
  let (rho, refresher, r) := Spec.PomFRIT.expandSeed (toL pk.digest) (toL msg) (toL seed)
  let rho := if rhoOverride.isEmpty then toBA rho else rhoOverride
  let com := toBA (Spec.PomFRIT.commitRefresher refresher)
  let dst := toBA (Spec.makeDst "pomf" 0 'p' '0')
  let pend := Prover.voleGen Hashes.shake c.T p (mu Hashes.shake none dst) (toBA r) rho com
  let st := pomfritRedeem pk (pend.proof ++ com ++ toBA refresher) msg c.layouts.pomfrit
  match Prover.proveCommit Hashes.shake st s pend with
  | .ok pf => (checkCorrelation c.T pend pf).map fun _ => pf
  | .error e => .error e

def pomfrit (c : Ctx) (path : String) : IO Bool := do
  let ls ← readLines path
  let pk := UovPk.ofCompressed (unhex (get ls "pk"))
  let mut ok := true
  let recs := records ls "seed"
  let n := (pomfritParams c.layouts.pomfrit).proofBytes
  for i in [0:recs.size] do
    let r := recs[i]!
    let sig := unhex (get r "signature")
    let msg := unhex (get r "msg")
    let seed := unhex (get r "seed")
    let s := unhex (get r "response")
    let st := pomfritRedeem pk sig msg c.layouts.pomfrit
    ok := (← run c s!"pomfrit {i}" st (some (sig.extract 0 n)) fun _ =>
      pomfritProve c pk msg seed s ByteArray.empty) && ok
    if i == 0 then
      ok := (← runBad c s!"pomfrit {i}, response bit 5 flipped" fun _ =>
        pomfritProve c pk msg seed (flipBit s 5) ByteArray.empty) && ok
  return ok

/-! ## A UOV preimage sampler (test only)

Random statements of the three UOV relations need preimages `P(s) = t`. With the oil space of a
compact secret key (`pk_seed ‖ O = SHAKE256(sk_seed)`, `Keygen.compressedPk`; the oil vectors are
`(O_j, e_j)`, on which `P` vanishes, checked), `P(x₀ + Σ_j y_j (O_j, e_j)) = P(x₀) + Σ_j y_j B(x₀,
(O_j, e_j))` for a random vinegar vector `x₀ = (a, 0)`, a linear system in `y` over GF(256). This is
not pqov's `derive_preimage` (its outputs are not reproduced); every preimage is checked with
`publicMapBytes`, which is in turn checked against `Spec.Ratatouille.uovEval`. -/

/-- The monomials `(i, j, offset)` of the expanded key (`UOV.forEachMonomial 119 45`). -/
def monos : Array (Nat × Nat × Nat) :=
  (Arith.UOV.forEachMonomial 119 45).toArray.map fun m => (m.i, m.j, m.off)

@[inline] def gmul (a b : UInt8) : UInt8 := Keygen.mulTab.get! (256 * a.toNat + b.toNat)

/-- `P(x)` (45 bytes) for the expanded key `pk`, over arrays. -/
def publicMapBytes (pk : UovPk) (x : ByteArray) : ByteArray := Id.run do
  let mut acc := Prover.zeros 45
  for (i, j, off) in monos do
    let a := gmul (x.get! i) (x.get! j)
    if a != 0 then acc := Keygen.madd acc pk.expanded 0 off a
  return acc

def xorB (a b : ByteArray) : ByteArray := ⟨(Array.range a.size).map fun k => a.get! k ^^^ b.get! k⟩

/-- The oil vectors `(O_j, e_j)`, `j < 45`, of a compact secret key. -/
def oilVectors (sk : ByteArray) : Array ByteArray :=
  let O := (Spec.SHAKE.shake256 sk (16 + 74 * 45)).extract 16 (16 + 74 * 45)
  (Array.range 45).map fun j =>
    ⟨(Array.range 119).map fun k =>
      if k < 74 then O.get! (74 * j + k) else if k - 74 == j then 1 else 0⟩

/-- Solve `A y = b` over GF(256) (`A` given by its 45 columns), or `none` if singular. -/
def solve (cols : Array ByteArray) (b : ByteArray) : Option ByteArray := Id.run do
  -- Rows of the augmented matrix.
  let mut rows : Array ByteArray := (Array.range 45).map fun r =>
    ⟨((Array.range 45).map fun j => cols[j]!.get! r).push (b.get! r)⟩
  for col in [0:45] do
    let some piv := (List.range' col (45 - col)).find? (fun r => rows[r]!.get! col != 0)
      | return none
    let tmp := rows[col]!
    rows := (rows.set! col rows[piv]!).set! piv tmp
    let inv := AES.ginv (rows[col]!.get! col)
    rows := rows.set! col ⟨rows[col]!.data.map (gmul inv)⟩
    for r in [0:45] do
      let f := rows[r]!.get! col
      if r != col && f != 0 then
        rows := rows.set! r (xorB rows[r]! ⟨rows[col]!.data.map (gmul f)⟩)
  return some ⟨rows.map (·.get! 45)⟩

/-- A preimage of `t` under the key of the compact secret key `sk` (randomness from `label`). -/
def sample (sk : ByteArray) (pk : UovPk) (t : ByteArray) (label : String) : Option ByteArray :=
  (List.range 8).findSome? fun attempt =>
    let x0 := rnd s!"{label} vinegar {attempt}" 74 ++ Prover.zeros 45
    let y0 := publicMapBytes pk x0
    let oil := oilVectors sk
    let cols := oil.map fun o => xorB (publicMapBytes pk (xorB x0 o)) y0
    (solve cols (xorB t y0)).map fun y =>
      (List.range 45).foldl (fun s j => xorB s ⟨oil[j]!.data.map (gmul (y.get! j))⟩) x0

/-- The sampler's checks: `P` vanishes on the oil vectors and `publicMapBytes` is
`Spec.Ratatouille.uovEval`. -/
def sampleOk (sk : ByteArray) (pk : UovPk) : Bool :=
  let x := rnd "uov eval check" 119
  (oilVectors sk).all (fun o => publicMapBytes pk o == Prover.zeros 45) &&
    publicMapBytes pk x ==
      ⟨(Spec.Ratatouille.uovEval pk.map (Vector.ofFn fun k => x.get! k.1)).toArray⟩

/-- Random statements of all five relations (completeness smoke test): fresh seeds and contexts,
the issuers' preimages from `sample`. `mousSks` are Moussaka Anchor keys (the issuer is one of
them), `rataSk` a Ratatouille issuer key, `pomSk` a PomFRIT Signer key (compact secret keys). -/
def randomUov (c : Ctx) (k : Nat) (mousSks : List ByteArray) (rataSk pomSk : ByteArray) :
    IO Bool := do
  let mut ok := true
  -- Moussaka: issue, sign, redeem.
  let anchors := mousSks.map UovPk.ofSecret
  let issuer := k % mousSks.length
  let ctxIss := toL (rnd s!"rmoussaka ctx_iss {k}")
  let ctxRed := toL (rnd s!"rmoussaka ctx_red {k}")
  let (nf, rr, _) := Spec.Moussaka.expandIssueSeed (toL (rnd s!"rmoussaka seed {k}" 32))
  let t := Spec.Moussaka.com nf ctxIss ctxRed rr
  let pkI := UovPk.ofSecret mousSks[issuer]!
  let some s := sample mousSks[issuer]! pkI (toBA t) s!"rmoussaka {k}"
    | IO.eprintln "FAIL sampler (moussaka)"; return false
  ok := (← Vectors.check s!"random moussaka {k}: P(s) = t" (publicMapBytes pkI s == toBA t)) && ok
  let cd := rnd s!"rmoussaka cd {k}" 32
  let st := moussakaRedeem anchors (toBA nf) (toBA ctxIss) (toBA ctxRed) cd c.layouts.moussaka
  ok := (← run c s!"random moussaka redeem {k} ({anchors.length} anchors, issuer {issuer})" st none
    fun _ => proveChecked c.T st
      (toBA (Spec.Moussaka.encodeRedeemWitness nf ctxIss ctxRed rr (toL s) issuer))
      (rnd s!"rmoussaka rho {k}")) && ok
  -- Ratatouille: issue, sign `tag(c, 0)`, spend.
  let pk := UovPk.ofSecret rataSk
  let vec {n : Nat} (b : ByteArray) : Spec.Ratatouille.Bytes n := Vector.ofFn fun i => b.get! i.1
  let ctx : Spec.Ratatouille.Context := vec (rnd s!"rratatouille ctx {k}")
  let tInit : UInt64 := 1000 + k.toUInt64
  let (rnf, ro, _) := Spec.Ratatouille.expandSeed Spec.Ratatouille.issueSeedDst
    (vec (rnd s!"rratatouille seed {k}" 32))
  let cm := Spec.Ratatouille.com rnf ctx tInit ro
  let tg : ByteArray := ⟨(Spec.Ratatouille.tag cm 0).toArray⟩
  let some rs := sample rataSk pk tg s!"rratatouille {k}"
    | IO.eprintln "FAIL sampler (ratatouille)"; return false
  let d : UInt64 := 7 + k.toUInt64
  let some t' := Spec.Ratatouille.clientCheck tInit 0 d
    | IO.eprintln "FAIL clientCheck"; return false
  let (nf', r', _) := Spec.Ratatouille.expandSeed Spec.Ratatouille.spendSeedDst
    (vec (rnd s!"rratatouille spend seed {k}" 32))
  let w : Spec.Ratatouille.SpendWitness := ⟨tInit, ro, 0, vec rs, nf', t', r'⟩
  let cNext := Spec.Ratatouille.com nf' ctx t' r'
  let sst := ratatouilleSpend pk ⟨rnf.toArray⟩ d.toNat ⟨cNext.toArray⟩ ⟨ctx.toArray⟩ c.layouts.ratatouille
  ok := (← run c s!"random ratatouille spend {k}" sst none fun _ =>
    proveChecked c.T sst (toBA (Spec.Ratatouille.encodeSpendWitness rnf w d ctx))
      (rnd s!"rratatouille rho {k}")) && ok
  -- PomFRIT: step 1, the Signer's preimage of `h ⊕ r`, step 2.
  let ppk := UovPk.ofSecret pomSk
  let msg := rnd s!"rpomfrit msg {k}" (k + 3)
  let p := pomfritParams c.layouts.pomfrit
  let (_, refresher, r) := Spec.PomFRIT.expandSeed (toL ppk.digest) (toL msg)
    (toL (rnd s!"rpomfrit seed {k}" 32))
  let com := toBA (Spec.PomFRIT.commitRefresher refresher)
  let dst := toBA (Spec.makeDst "pomf" 0 'p' '0')
  let pend := Prover.voleGen Hashes.shake c.T p (mu Hashes.shake none dst) (toBA r)
    (rnd s!"rpomfrit rho {k}") com
  let sig1 := pend.proof ++ com ++ toBA refresher
  let pst := pomfritRedeem ppk sig1 msg c.layouts.pomfrit
  let h := pomfritTarget p ppk.digest pend.chal1 sig1 msg
  let some ps := sample pomSk ppk (xorB h (toBA r)) s!"rpomfrit {k}"
    | IO.eprintln "FAIL sampler (pomfrit)"; return false
  ok := (← run c s!"random pomfrit {k}" pst none fun _ =>
    match Prover.proveCommit Hashes.shake pst ps pend with
    | .ok pf => (checkCorrelation c.T pend pf).map fun _ => pf
    | .error e => .error e) && ok
  if (s!"random pomfrit {k}").startsWith c.filter then
    -- The whole signature through PomFRIT's `verify` (refresher check included).
    match Prover.proveCommit Hashes.shake pst ps pend with
    | .ok pf =>
      ok := (← Vectors.check s!"random pomfrit {k}: pomfritVerify"
        (pomfritVerify Hashes.shake c.T ppk (pf ++ com ++ toBA refresher) msg
          c.layouts.pomfrit).accept) && ok
    | .error _ => ok := false
  return ok

/-- Random Moussaka and Ratatouille issuance statements (completeness smoke test). -/
def random (c : Ctx) (n : Nat) : IO Bool := do
  let mut ok := true
  for k in [0:n] do
    let seed := toL (rnd s!"moussaka seed {k}" 32)
    let ctxIss := toL (rnd s!"moussaka ctx_iss {k}")
    let ctxRed := toL (rnd s!"moussaka ctx_red {k}")
    let (nf, rr, rho) := Spec.Moussaka.expandIssueSeed seed
    let t := Spec.Moussaka.com nf ctxIss ctxRed rr
    let st := moussakaIssue (toBA t) (toBA ctxIss) c.layouts.moussaka
    ok := (← run c s!"random moussaka issue {k}" st none fun _ =>
      proveChecked c.T st (toBA (Spec.Moussaka.encodeIssueWitness nf ctxIss ctxRed rr))
        (toBA rho)) && ok
    let rseed := rnd s!"ratatouille seed {k}" 32
    let rctx := rnd s!"ratatouille ctx {k}"
    let tInit :=
      (rnd s!"ratatouille t_init {k}" 2).toList.foldr (fun b acc => acc * 256 + b.toNat) 1
    let (rnf, ro, rrho) := Spec.Ratatouille.expandSeed Spec.Ratatouille.issueSeedDst
      (Vector.ofFn fun i => rseed.get! i.1)
    let ctxV : Spec.Ratatouille.Context := Vector.ofFn fun i => rctx.get! i.1
    let cm := Spec.Ratatouille.com rnf ctxV tInit.toUInt64 ro
    let rst := ratatouilleIssue ⟨cm.toArray⟩ tInit rctx c.layouts.ratatouille
    ok := (← run c s!"random ratatouille issue {k}" rst none fun _ =>
      proveChecked c.T rst
        (toBA (Spec.Ratatouille.encodeIssueWitness rnf ctxV tInit.toUInt64 ro))
        ⟨rrho.toArray⟩) && ok
  return ok

def main (args : List String) : IO UInt32 := do
  let tests := args.headD "../tests"
  let layouts := Layouts.ofArg (args.getD 1 "")
  let filter := args.getD 2 ""
  let mousPath := s!"{tests}/moussaka/moussaka_kat.txt"
  let rataPath := s!"{tests}/ratatouille/ratatouille_kat.txt"
  let sks :=
    (getAll (← readLines mousPath) "anchor_sk") ++ (getAll (← readLines rataPath) "issuer_sk")
  let t0 ← IO.monoMsNow
  let mut cpks : Std.HashMap String ByteArray := {}
  for sk in sks do
    if !cpks.contains sk then cpks := cpks.insert sk (Keygen.compressedPk (unhex sk))
  let t1 ← IO.monoMsNow
  IO.println s!"UOV key generation: {cpks.size} keys ({t1 - t0} ms)"
  IO.println s!"Proof layout: {layouts.describe}"
  let c : Ctx :=
    { T := CrtGen.tables, cpks := cpks, layouts := layouts, filter := filter,
      reproduced := ← IO.mkRef 0, verified := ← IO.mkRef 0 }
  let ok1 ← moussaka c mousPath
  let ok2 ← ratatouille c rataPath
  let ok3 ← pomfrit c s!"{tests}/pomfrit/pomfrit_kat.txt"
  let ok4 ← random c 2
  -- Random statements of the UOV relations, with keys from the KAT files.
  let mousRecs := records (← readLines mousPath) "issue_seed"
  let mousSks := (getAll mousRecs[1]! "anchor_sk").toList.map unhex
  let rataSk := unhex (get (← readLines rataPath) "issuer_sk")
  let pomSk := unhex (get (← readLines s!"{tests}/pomfrit/pomfrit_kat.txt") "sk")
  let mut ok5 ← Vectors.check "UOV sampler: P vanishes on the oil space, publicMapBytes = uovEval"
    (sampleOk rataSk (UovPk.ofSecret rataSk))
  for k in [0:2] do
    ok5 := (← randomUov c k mousSks rataSk pomSk) && ok5
  let t2 ← IO.monoMsNow
  let ok := ok1 && ok2 && ok3 && ok4 && ok5
  IO.println s!"Lean prover: {← c.reproduced.get} KAT proofs reproduced byte for byte, \
    {← c.verified.get} Lean proofs accepted by the Lean verifier, {if ok then "ok" else "FAILED"} \
    ({t2 - t1} ms)"
  return if ok then 0 else 1

end VoleMole.Verifier.ProverKats
