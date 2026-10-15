import VoleMole.Verifier.Prover

/-!
# The zero-knowledge simulator and the ideal-tape prover (executable)

`lean/docs/zk.md` §5–§6 for the executable prover `Verifier/Prover.lean`. Everything here runs
(`lake exe zk_sim`, `ZK/SimKats.lean`); the theorems are in `ZK/SimAccept.lean` (the verifier
accepts simulated proofs under the programmed oracle), `ZK/IdealSim.lean` (with the ideal tape, the
prover's output distribution is the simulator's) and `ZK/TapeOf.lean` (the prover is the
ideal-tape prover at the tape its own run determines).

## Tapes

A tape is a tuple of byte blocks (`Bytes n = Fin n → UInt8`), so that "uniform" is the uniform
distribution on a finite type.

* `Shared`: what the simulator and the ideal prover sample alike: `iv_pre`, the `H₂³` answers at the
  grinding counters `0, 1, …, 2³² − 1` (`grind`), the 17 hidden leaves' commitments and 105 opened
  seeds (the first `openCount Δ` are used).
* `SimFields`: the simulator's uniform proof fields (`zk.md` H5–H7): the corrections `c_i`,
  `c_mult`, the VOLE check `ũ`, the witness correction `d` and the QuickSilver proof `ã`.
* `Pads`: the ideal prover's secrets: `u^{(0)}` on the witness rows (`u0w`) and on the dedicated
  label rows (`θ`, the label offset `Θ`; empty on `main`), `u^{(i)}` (`i ≥ 1`) on the corrected rows,
  every `u^{(i)}` on the mask rows (byte `VOLE_CORRECTION_BYTES + m` holds mask `m`'s 8 rows) and on
  the remaining rows, the root PRG's `u_hi` bytes, and the `H₅` answers at the sibling labels.

## Grinding (`zk.md` H2)

`firstHit g`: the first counter `c` whose `H₂³` answer `g c` is in the acceptance set `A` (`accepts`:
the 8 grinding bits are zero and the opening needs at most `T_OPEN = 105` seeds, `openCount`, which
depends on `Δ` only). The prover's `(ctr, Δ)` is the first hit of its `H₂³` answers
(`grind_and_open`); with uniform answers this is `Grinding.lean`'s `IsFirstHit` law, so the
simulator samples `(ctr, Δ)` the same way, from its own `grind`, before anything else.

## The simulator (`zk.md` §5, `simulate`, `simulateRO`)

From the statement and its coins only: `(ctr, Δ)` from `grind`, the opening from the sampled
commitments and seeds (`openingOf`, the layout of `one_tree_bavc::open`), uniform `c_i`, `c_mult`,
`ũ`, `d`, `ã`. `simulateRO` also **programs the random oracle**: it runs the verifier on the
simulated proof with the given hashes `Hs` (which yields the verifier's `chal2` and `qs_check`, as
`zk.md` §5 computes them "as the verifier does") and returns `Hs` with `H₂³` answering
`chal2 ‖ qs_check ‖ ã ‖ ctr ‖ 11 ↦ Δ` and, for each counter `c < ctr`, `… ‖ c ‖ 11 ↦ grind c`
(`program`). Only `H₂³` changes, and only at points that start with the fresh `chal2`.

## The ideal-tape prover (`proveIdeal`, hybrid H6/H7 with H3)

The prover's computation, step for step (`Prover.voleGen`, `Prover.proveCommit`), with its random
sources replaced by the tape as after hybrids H1–H4:

* `iv_pre`, the opening (seeds and hidden commitments) and `(ctr, Δ)` from `Shared` (H1, H2, H4);
* the small VOLEs' inputs `u^{(i)}` from `Pads` (H4: each hidden leaf's PRG output pads its tree);
  the prover's tags are `v = q + Δ·u`, with `q` the verifier's key columns (`convertToVoleAt` from
  the opening and the corrections; `vole_v_unique`);
* `u_hi` from `Pads`;
* the `H₅` answer at the sibling label `L^{1−γ_e}_e` from `Pads` (`sib`; H6), at the forced label
  `L^{γ_e}_e` from `Hs`;
* the lifted tags and the masks' tags as the verifier recomputes them (H3): `v_r = q_r + u_r Δ'`,
  `ṽ_mask[m] = q_mask[m] + u_mask[m] Δ'`, with `q`, `q_mask` the verifier's
  (`crtReconstructAt`). `TapeOf.lean` shows these are the prover's own at the real tape (from
  `Bridge.prover_row` and the CRT VOLE's correlation `Bridge.CrtComplete`).

Everything else (`c_i`, `c_mult`, `chal1`, `ũ`, `h_V`, `d`, `chal2`, QuickSilver) is the prover's
code. The ideal prover uses every hash of `Hs` except `H₂³` and `H₅` at the sibling labels, and the
simulator's proof uses none.
-/

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Arith

/-! ## Byte blocks -/

/-- `n` bytes, a component of a tape. -/
abbrev Bytes (n : Nat) := Fin n → UInt8

/-- The byte string of a block. -/
def ba {n : Nat} (b : Bytes n) : ByteArray := ⟨Array.ofFn b⟩

/-- A byte string as a block of `n` bytes (zero-padded or truncated). -/
def blk (n : Nat) (b : ByteArray) : Bytes n := fun i => b.get! i

/-! ## The programmable oracle -/

/-- `Hs` with `H₂³` reprogrammed: the first entry `(x, y)` of `pts` with `x` the input answers `y`;
every other query is answered by `Hs`. -/
def program (Hs : Hashes) (pts : List (ByteArray × ByteArray)) : Hashes :=
  ⟨fun k x =>
    if k = .h23 then
      match pts.find? (fun q => q.1 == x) with
      | some q => q.2
      | none => Hs.hash k x
    else Hs.hash k x⟩

/-! ## Grinding -/

/-- The number of grinding counters (`grind_and_open` tries `ctr < 2³²`). -/
def nGrind : Nat := 2 ^ 32

/-- The number of seeds the opening at `Δ` reveals (`BAVC.openSeeds` counts them from `Δ` alone; the
tree argument is never inspected for the count). -/
def openCount (delta : ByteArray) : Nat :=
  (BAVC.openSeeds (Array.replicate BAVC.numNodes BAVC.zeroBlock) delta).size

/-- The grinding acceptance set `A`: zero grinding bits and an opening of at most `T_OPEN` seeds. -/
def accepts (delta : ByteArray) : Bool := delta.get! 15 == 0 && openCount delta ≤ 105

/-- The first counter whose `H₂³` answer `g c` is accepted, and that answer. -/
def firstHit (g : Fin nGrind → Bytes 16) : Option (Nat × Bytes 16) :=
  Prover.findFirst (fun c =>
    if h : c < nGrind then (if accepts (ba (g ⟨c, h⟩)) then some (c, g ⟨c, h⟩) else none)
    else none) nGrind 0

/-- The opening at `Δ` from the hidden leaves' commitments `coms` and the seeds `seeds` (the first
`openCount Δ` of them), in `one_tree_bavc::open`'s layout, zero-padded. -/
def openingOf (delta : ByteArray) (coms : Fin BAVC.tau → Bytes 32) (seeds : Fin 105 → Bytes 16) :
    ByteArray :=
  let hidden := (List.range BAVC.tau).foldl
    (fun acc i => acc ++ if h : i < BAVC.tau then ba (coms ⟨i, h⟩) else ByteArray.empty) ByteArray.empty
  let body := (List.range (openCount delta)).foldl
    (fun acc k => acc ++ if h : k < 105 then ba (seeds ⟨k, h⟩) else ByteArray.empty) hidden
  body ++ Prover.zeros (BAVC.openSize - body.size)

/-! ## Tapes -/

/-- The part of the tape the simulator and the ideal prover share: `iv_pre`, the grinding answers,
the hidden leaves' commitments and the opened seeds. -/
abbrev Shared := Bytes 16 × (Fin nGrind → Bytes 16) × (Fin BAVC.tau → Bytes 32) × (Fin 105 → Bytes 16)

/-- The simulator's uniform fields: `c_1 … c_16`, `c_mult`, `ũ`, `d`, `ã`. -/
abbrev SimFields (p : Params) :=
  Bytes (16 * p.correctionBytes) × Bytes (p.nMask * p.nMultBytes) × Bytes 64 ×
    Bytes p.witnessBytes × Bytes (16 * (p.qsDegree - 1))

/-- The simulator's coins. -/
abbrev SimCoins (p : Params) := Shared × SimFields p

/-- The number of label-row bytes (`16` with dedicated label rows, `0` on `main`). -/
def labelBytes (p : Params) : Nat := p.correctionBytes - p.witnessBytes

/-- The bytes of a column below the mask rows. -/
def restBytes (p : Params) : Nat := p.colBytes - p.correctionBytes - p.nMask

/-- The ideal prover's secret pads: `u^{(0)}` on the witness rows and on the label rows, `u^{(i)}`
(`i ≥ 1`) on the corrected rows, every `u^{(i)}` on the mask rows and on the remaining rows,
`u_hi`, and the `H₅` answers at the sibling labels. -/
abbrev Pads (p : Params) :=
  Bytes p.witnessBytes × Bytes (labelBytes p) × (Fin (BAVC.tau - 1) → Bytes p.correctionBytes) ×
    (Fin BAVC.tau → Bytes p.nMask) × (Fin BAVC.tau → Bytes (restBytes p)) × Bytes p.nMask ×
    (Fin 312 → Bytes 4)

/-- The ideal prover's tape. -/
abbrev IdealTape (p : Params) := Shared × Pads p

/-- The bytes of `u^{(i)}` (one column, `colBytes` bytes when the sizes add up). -/
def usBytes (p : Params) (t : Pads p) (i : Nat) : ByteArray :=
  (if i = 0 then ba t.1 ++ ba t.2.1
   else if h' : i - 1 < BAVC.tau - 1 then ba (t.2.2.1 ⟨i - 1, h'⟩) else ByteArray.empty) ++
  (if h : i < BAVC.tau then ba (t.2.2.2.1 ⟨i, h⟩) ++ ba (t.2.2.2.2.1 ⟨i, h⟩) else ByteArray.empty)

/-! ## The simulator -/

/-- The ctr field: `ctr` as 4 little-endian bytes. -/
def ctrBytes (ctr : Nat) : ByteArray := AES.pushLE32 ByteArray.empty ctr.toUInt32

/-- The public part of a proof, from the shared tape and the grinding outcome. -/
def publicFields (s : Shared) (ctr : Nat) (delta : Bytes 16) : Prover.Fields :=
  { corrections := .empty, cmult := .empty, voleCheck := .empty, correction := .empty,
    qsProof := .empty, opening := openingOf (ba delta) s.2.2.1 s.2.2.2, delta := ba delta,
    ivPre := ba s.1, ctr := ctrBytes ctr }

/-- **The simulated proof** (`zk.md` §5): the grinding outcome first, then the public part and
uniform `c_i`, `c_mult`, `ũ`, `d`, `ã`. Neither the witness nor any hash is used. -/
def simulate (p : Params) (c : SimCoins p) : Except String ByteArray :=
  match firstHit c.1.2.1 with
  | none => .error "grinding failed"
  | some (ctr, delta) =>
    .ok (Prover.assemble p { publicFields c.1 ctr delta with
      corrections := ba c.2.1, cmult := ba c.2.2.1, voleCheck := ba c.2.2.2.1,
      correction := ba c.2.2.2.2.1, qsProof := ba c.2.2.2.2.2 })

/-- The `H₂³` points to program for a proof: the verifier's `chal3` input for the proof's own
counter `ctr` (answered by `Δ`), then the inputs for the counters `c < ctr` (answered by the
rejected `grind c`). `chal2` and `qs_check` are the verifier's, with the hashes `Hs`. -/
def programPoints (Hs : Hashes) (T : CrtTables) (st : Statement) (proof : ByteArray)
    (g : Fin nGrind → Bytes 16) (ctr : Nat) : List (ByteArray × ByteArray) :=
  let pf : Proof := { params := st.params, bytes := proof }
  let tr := verify Hs T st proof
  ((tr.chal2 ++ tr.qsCheck ++ pf.qsProof ++ pf.ctr).push 11, pf.delta) ::
    (List.range ctr).map fun k =>
      ((tr.chal2 ++ tr.qsCheck ++ pf.qsProof ++ ctrBytes k).push 11,
        if h : k < nGrind then ba (g ⟨k, h⟩) else ByteArray.empty)

/-- **The simulator in the programmable random-oracle model**: the simulated proof and the hashes
`Hs` with `H₂³` programmed at the proof's grinding points (`programPoints`). -/
def simulateRO (Hs : Hashes) (T : CrtTables) (st : Statement) (c : SimCoins st.params) :
    Except String (ByteArray × Hashes) := do
  let proof ← simulate st.params c
  let ctr := ((firstHit c.1.2.1).map (·.1)).getD 0
  return (proof, program Hs (programPoints Hs T st proof c.1.2.1 ctr))

/-! ## The ideal-tape prover -/

/-- `u_mask[m] = W_CRT · u_low[m] ⊕ M_tree · u_hi[m]` (`Prover.uMaskOf` with the root PRG's output
`hi` given). -/
def uMaskOfHi (p : Params) (T : CrtTables) (hi : ByteArray) (us : Array (Array UInt64)) :
    Array W128 :=
  let ell := p.correctionRows
  (Array.range p.nMask).map fun m =>
    let low : Nat → Bool := fun c =>
      let i := BAVC.treeOf c
      wbit us[i]! (ell + 8 * m + (c - BAVC.bitOffset i))
    (W128.rowMul low 120 T.wCrt).xor
      (CrtGen.w128OfNat (CrtGen.pmul (hi.get! m).toNat Prover.mTree))

/-- The prover's tag columns from the verifier's key columns: `v_c = q_c + Δ_c · u` (exact on the
corrected rows, the only rows the gate labels read). -/
def tagCols (dbit : Nat → Bool) (qcols : Array (Array UInt64)) (u : Array UInt64) :
    Array (Array UInt64) :=
  (Array.range 128).map fun c => if dbit c then xorWords qcols[c]! u else qcols[c]!

/-- The gate hashes `h^b_e` (`b = 0`: of `L⁰_e`, `b = 1`: of `L¹_e = L⁰_e ⊕ Θ`): `H₅` from `Hs` at
the forced label (`b = γ_e`), the tape's `sib e` at the sibling label. -/
def gateHashesIdeal (Hs : Hashes) (gamma : Array UInt64) (b : Bool) (ins : List ByteArray)
    (sib : Fin 312 → Bytes 4) : Array UInt32 :=
  gateWords ((List.range 312).map fun e =>
    if wbit gamma e == b then Hs.hash .h5 (ins.getD e ByteArray.empty)
    else if h : e < 312 then ba (sib ⟨e, h⟩) else ByteArray.empty)

/-- The public values of the ideal prover's run after `(ctr, Δ)`: `μ₁`, `iv`, the opening, the
verifier's leaves and `vole_commit_check`. -/
structure Pub where
  mu1 : ByteArray
  iv : ByteArray
  opening : ByteArray
  leaves : BAVC.Leaves
  check : ByteArray

/-- The public values (`Pub`) from the shared tape and `Δ`. -/
def pubOf (Hs : Hashes) (st : Statement) (s : Shared) (delta : Bytes 16) : Pub :=
  let mu1 := st.mu1 Hs
  let iv := Hs.hash .h4 ((ba s.1 ++ mu1).push 4)
  let opening := openingOf (ba delta) s.2.2.1 s.2.2.2
  let leaves := (BAVC.reconstruct iv opening (ba delta)).getD ⟨.empty, .empty⟩
  { mu1, iv, opening, leaves, check := BAVC.check (Hs.hash .h1) leaves.coms }

/-- The verifier's key columns from the corrections (`convertToVoleAt` at `Δ`, with the opening's
leaves). -/
def qcolsOf (st : Statement) (P : Pub) (delta : Bytes 16) (corrections : ByteArray) :
    Array (Array UInt64) :=
  convertToVoleAt st.params (BAVC.deltaBit (ba delta)) (fun i =>
    corrections.extract ((i - 1) * st.params.correctionBytes) (i * st.params.correctionBytes))
    P.iv (leafKey P.leaves)

/-! ### The rest of the ideal prover's run -/

section Tail

variable (Hs : Hashes) (T : CrtTables) (st : Statement) (s : Shared) (ctr : Nat)
  (delta : Bytes 16)

/-- The verifier's CRT reconstruction from the corrections and `c_mult`. -/
def tCrt (c cmult : ByteArray) : CrtOut :=
  crtReconstructAt (Hs.hash .h5) st.params (BAVC.deltaBit (ba delta))
    (Prover.fit cmult (st.params.nMask * st.params.nMultBytes)) T (pubOf Hs st s delta).iv
    (qcolsOf st (pubOf Hs st s delta) delta c)

/-- The lifted `Δ`. -/
def tDL : GF128 := (W128.rowMul (BAVC.deltaBit (ba delta)) 120 T.wCrt).toGF

/-- The prover's tags on the corrected rows, as the verifier recomputes them. -/
def tVRows (c cmult : ByteArray) (ubits : Array Bool) : Array W128 :=
  let crt := tCrt Hs T st s delta c cmult
  let dL := tDL T delta
  (Array.range st.params.correctionRows).map fun r =>
    Prover.W128.ofGF (crt.rows[r]!.toGF + (if ubits[r]! then dL else 0))

/-- The masks' tags, as the verifier recomputes them. -/
def tVMask (c cmult : ByteArray) (uMask : Array W128) : Array W128 :=
  let crt := tCrt Hs T st s delta c cmult
  let dL := tDL T delta
  (Array.range st.params.nMask).map fun m =>
    Prover.W128.ofGF (crt.qMask[m]!.toGF + uMask[m]!.toGF * dL)

/-- The fields before the VOLE check. -/
def tF0 (c cmult : ByteArray) : Prover.Fields :=
  { publicFields s ctr delta with
    corrections := c, cmult := cmult, opening := .empty, delta := .empty, ctr := .empty }

/-- `chal1`. -/
def tC1 (c cmult : ByteArray) : ByteArray :=
  let P := pubOf Hs st s delta
  chal1 Hs { params := st.params, bytes := Prover.assemble st.params (tF0 s ctr delta c cmult) }
    P.mu1 P.check st.binder1

/-- The rows of `u` as field elements. -/
def tURows (ubits : Array Bool) : Array W128 :=
  (Array.range st.params.correctionRows).map fun r => if ubits[r]! then ⟨1, 0⟩ else W128.zero

/-- The VOLE check `ũ`. -/
def tUt (c cmult : ByteArray) (ubits : Array Bool) (uMask : Array W128) : Array GF128 :=
  voleHashReceiver st.params (tC1 Hs st s ctr delta c cmult) (tURows st ubits) uMask 0
    (Prover.zeros 64)

/-- The fields before QuickSilver. -/
def tF1 (c cmult : ByteArray) (ut : Array GF128) (d : ByteArray) : Prover.Fields :=
  { tF0 s ctr delta c cmult with voleCheck := Prover.gfsToBytes ut, correction := d }

end Tail

/-- **The rest of the ideal prover's run**, from the corrections, `c_mult`, `u_mask`, the bits of
`u` on the corrected rows (`ubits`) and the witness correction `d`: the tags as the verifier
recomputes them (H3, `tVRows`, `tVMask`), `chal1`, the VOLE check, `chal2`, QuickSilver, the
proof. -/
def idealTail (Hs : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray) (s : Shared)
    (ctr : Nat) (delta : Bytes 16) (corrections cmult : ByteArray) (uMask : Array W128)
    (ubits : Array Bool) (correction : ByteArray) : Except String ByteArray := do
  let p := st.params
  let c1 := tC1 Hs st s ctr delta corrections cmult
  let vRows := tVRows Hs T st s delta corrections cmult ubits
  let vMask := tVMask Hs T st s delta corrections cmult uMask
  let ut := tUt Hs st s ctr delta corrections cmult ubits uMask
  let hV := voleHashReceiver p c1 vRows vMask 0 (Prover.zeros 64)
  let pf1 : Proof :=
    { params := p, bytes := Prover.assemble p (tF1 s ctr delta corrections cmult ut correction) }
  let c2 := chal2 Hs pf1 c1 hV (st.muDelayed Hs c1) st.binder2
  let values := st.values c1 (st.combBytes Hs c2)
  let (_, aT) ← Prover.qsProve pf1 c2 values vRows vMask uMask w
  return Prover.assemble p
    { tF1 s ctr delta corrections cmult ut correction with
      qsProof := Prover.gfsToBytes aT, delta := ba delta, ctr := ctrBytes ctr,
      opening := (pubOf Hs st s delta).opening }

/-- The ideal prover's `c_mult` (`compute_v_gate`): the gate hashes with the tape's `H₅` answers at
the sibling labels (`gateHashesIdeal`), the prover's tags `v = q + Δ·u` for the labels. -/
def cmultIdeal (Hs : Hashes) (T : CrtTables) (st : Statement) (P : Pub) (delta : Bytes 16)
    (qcols : Array (Array UInt64)) (u : Array UInt64) (uMask : Array W128)
    (sib : Fin 312 → Bytes 4) : ByteArray :=
  let p := st.params
  let dbit := BAVC.deltaBit (ba delta)
  let cols := tagCols dbit qcols u
  let uPre : W128 := ⟨wordAt u p.labelRowOffset, wordAt u (p.labelRowOffset + 64)⟩
  let gamma := gammaOf T dbit
  let h0 := gateHashesIdeal Hs gamma false (Prover.gateInputsOff p T P.iv cols W128.zero) sib
  let h1 := gateHashesIdeal Hs gamma true (Prover.gateInputsOff p T P.iv cols uPre) sib
  Prover.cMultOf p h0 h1 uMask

/-- The small VOLEs' inputs `u^{(i)}`, as words. -/
def usOf (p : Params) (t : Pads p) : Array (Array UInt64) :=
  (Array.range BAVC.tau).map fun i => wordsOf (usBytes p t i)

/-- The corrections `c_i = u^{(0)} ⊕ u^{(i)}` (`Prover.correctionOf`). -/
def correctionsOf (p : Params) (us : Array (Array UInt64)) : ByteArray :=
  (List.range (BAVC.tau - 1)).foldl
    (fun acc i => acc ++ Prover.correctionOf p us[0]! us[i + 1]!) ByteArray.empty

/-- **The prover on the ideal tape**, after the grinding outcome `(ctr, Δ)`. -/
def idealCore (Hs : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray) (s : Shared)
    (ctr : Nat) (delta : Bytes 16) (t : Pads st.params) : Except String ByteArray :=
  let p := st.params
  let P := pubOf Hs st s delta
  let us := usOf p t
  let u := us[0]!
  let corrections := correctionsOf p us
  let uMask := uMaskOfHi p T (ba t.2.2.2.2.2.1) us
  let cmult := cmultIdeal Hs T st P delta (qcolsOf st P delta corrections) u uMask t.2.2.2.2.2.2
  let ub := bytesOfWords u
  let correction : ByteArray := ⟨(Array.range p.witnessBytes).map fun k => ub.get! k ^^^ w.get! k⟩
  idealTail Hs T st w s ctr delta corrections cmult uMask
    ((Array.range p.correctionRows).map (wbit u)) correction

/-- **The ideal-tape prover**: the grinding outcome from the tape first, then `idealCore`. -/
def proveIdeal (Hs : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)
    (t : IdealTape st.params) : Except String ByteArray :=
  if w.size != st.params.witnessBytes then .error "witness: wrong length"
  else match firstHit t.1.2.1 with
    | none => .error "grinding failed"
    | some (ctr, delta) => idealCore Hs T st w t.1 ctr delta t.2

/-! ## The tape of a real run -/

/-- The real witness correction `d` (`Prover.proveCommit`). -/
def realCorr (p : Params) (s : Prover.Pending) (w : ByteArray) : ByteArray :=
  ⟨(Array.range p.witnessBytes).map fun k => (bytesOfWords s.u).get! k ^^^ w.get! k⟩

/-- The real proof's fields before QuickSilver. -/
def realF1 (p : Params) (s : Prover.Pending) (w : ByteArray) : Prover.Fields :=
  { s.fields with correction := realCorr p s w }

/-- The real `chal2`. -/
def realC2 (Hs : Hashes) (st : Statement) (s : Prover.Pending) (w : ByteArray) : ByteArray :=
  chal2 Hs { params := st.params, bytes := Prover.assemble st.params (realF1 st.params s w) }
    s.chal1 s.hV (st.muDelayed Hs s.chal1) st.binder2

/-- The real grinding prefix `chal2 ‖ qs_check ‖ ã`. -/
def realPre (Hs : Hashes) (st : Statement) (s : Prover.Pending) (w : ByteArray) : ByteArray :=
  match Prover.qsProve { params := st.params, bytes := Prover.assemble st.params (realF1 st.params s w) }
      (realC2 Hs st s w) (st.values s.chal1 (st.combBytes Hs (realC2 Hs st s w)))
      s.vRows s.vMask s.uMask w with
  | .ok (check, aT) => realC2 Hs st s w ++ gfToBytes check ++ Prover.gfsToBytes aT
  | .error _ => ByteArray.empty

/-- The real run's `H₂³` answers at its grinding points. -/
def realGrind (Hs : Hashes) (pre : ByteArray) : Fin nGrind → Bytes 16 := fun c =>
  blk 16 (Hs.hash .h23 ((AES.pushLE32 pre c.val.toUInt32).push 11))

/-- The hidden leaves' commitments of a commitment at `Δ`, as tape blocks. -/
def comsOf (coms delta : ByteArray) (i : Fin BAVC.tau) : Bytes 32 :=
  let j := BAVC.leafOffset i + BAVC.deltaIndex delta i
  blk 32 (coms.extract (BAVC.hashLen * j) (BAVC.hashLen * j + BAVC.hashLen))

/-- The opened seeds at `Δ`, as tape blocks. -/
def seedsOf (t : Array ByteArray) (delta : ByteArray) (k : Fin 105) : Bytes 16 :=
  blk 16 ((BAVC.openSeeds t delta).getD k .empty)

/-- The small VOLEs' inputs `u^{(i)}` of a real run (all leaves), as bytes. -/
def realUs (p : Params) (s : Prover.Pending) : Array ByteArray :=
  (Array.range BAVC.tau).map fun i =>
    bytesOfWords (Prover.smallVoleUWords p s.iv i (leafKey s.leaves i))

/-- The `H₅` answers at the sibling labels (`L^{1−γ_e}_e`: `L⁰` if `γ_e`, else `L¹`). -/
def sibAnswers (Hs : Hashes) (gamma : Array UInt64) (in0 in1 : List ByteArray) : Array ByteArray :=
  (Array.range 312).map fun e => Hs.hash .h5 ((if wbit gamma e then in0 else in1).getD e .empty)

/-- The pads from the columns' bytes, `u_hi` and the sibling answers. (Not inlined, so that the
smoke test computes its arguments once.) -/
@[noinline] def padsOfArrays (p : Params) (us : Array ByteArray) (hi : ByteArray)
    (sib : Array ByteArray) : Pads p :=
  let cb := p.correctionBytes
  (blk p.witnessBytes us[0]!, blk (labelBytes p) (us[0]!.extract p.witnessBytes cb),
    fun i => blk cb us[i.val + 1]!, fun i => blk p.nMask (us[i.val]!.extract cb (cb + p.nMask)),
    fun i => blk (restBytes p) (us[i.val]!.extract (cb + p.nMask) p.colBytes), blk p.nMask hi,
    fun e => blk 4 sib[e.val]!)

/-- The pads of a real run at `Δ`: the small VOLEs' inputs (all leaves), the root PRG's `u_hi`,
and `H₅` at the sibling labels. -/
def realPads (Hs : Hashes) (T : CrtTables) (p : Params) (s : Prover.Pending) (delta : ByteArray) :
    Pads p :=
  let cols := Prover.senderColumns p s.iv (leafKey s.leaves)
  let uPre : W128 := ⟨wordAt s.u p.labelRowOffset, wordAt s.u (p.labelRowOffset + 64)⟩
  padsOfArrays p (realUs p s)
    (AES.prg s.seed s.iv (((1 : UInt32) <<< 31) - 1) 0 ((8 * p.nMask + 127) / 128))
    (sibAnswers Hs (gammaOf T (BAVC.deltaBit delta)) (Prover.gateInputsOff p T s.iv cols W128.zero)
      (Prover.gateInputsOff p T s.iv cols uPre))

/-- **The tape a real run determines** (`Prover.prove` with `rho` and the witness prefix of
`prefixBytes` bytes that seeds `H₃`): `iv_pre`, the `H₂³` answers at the run's grinding points, the
hidden commitments and the opened seeds at the run's `Δ`, and `realPads`. `TapeOf.lean` proves
`prove = proveIdeal ∘ tapeOf`; `zk_sim` checks it on the KAT runs. -/
def tapeOf (Hs : Hashes) (T : CrtTables) (st : Statement) (w rho : ByteArray)
    (prefixBytes : Nat := st.params.witnessBytes) : IdealTape st.params :=
  let s := Prover.voleGen Hs T st.params (st.mu1 Hs) (w.extract 0 prefixBytes) rho st.binder1
  let g := realGrind Hs (realPre Hs st s w)
  let delta := ba ((firstHit g).map (·.2) |>.getD fun _ => 0)
  ((blk 16 s.ivPre, g, comsOf s.leaves.coms delta, seedsOf s.tree delta),
   realPads Hs T st.params s delta)

end VoleMole.ZK.Sim
