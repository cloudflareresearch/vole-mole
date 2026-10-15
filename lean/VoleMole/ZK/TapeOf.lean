import VoleMole.ZK.TapeLemmas
import VoleMole.ZK.QsIdeal
import VoleMole.ZK.CMult

/-!
# The real prover is the ideal-tape prover at its own tape (`lean/docs/zk.md` H1–H4, H6)

**`prove_eq_proveIdeal`**: `Prover.prove Hs T st w rho = proveIdeal Hs T st w (tapeOf Hs T st w rho)`
for every hash record with the domains' output lengths, every `rho` and every witness satisfying
the statement's system. More generally (`proveCommit_eq_proveIdeal`), step 2 of a run whose step 1
had the witness prefix `wPrefix` is the ideal-tape prover at the run's tape (`tapeAt`) for any
suffix, and the ideal run's step-1 values at that tape are the real ones at every accepted `Δ`
(`step1_real`); `ZK/TwoPhase.lean` uses both for PomFRIT's two steps. So the real prover's output distribution is the ideal-tape prover's under
the distribution of `tapeOf … rho`, and the random-oracle and PRG/ideal-cipher hops H1–H4 and H6
are exactly the claim that this tape is close to uniform (`ZK/Exec.lean`).

The pieces (all at the real run's values):

* the tape's pads reassemble the small VOLEs' inputs `u^{(i)}` (`usBytes_reassemble`), so the ideal
  prover's corrections, `u`, `u_mask` and `d` are the real ones;
* the tape's commitments and seeds reassemble the opening (`openingOf_eq`), whose reconstruction is
  the real leaves off the hidden ones (`BAVCComplete`), so the verifier's key columns are the real
  ones (`Bridge.convertToVoleAt_congr_key`);
* the prover's tags `v = q + Δ·u` (`tagCols`) agree with the real ones on the label rows
  (`Bridge.prover_column`), so the gate inputs and hence `c_mult` are the real ones; the tape's
  sibling answers are the `H₅` answers the real run reads;
* the tags as the verifier recomputes them are the real ones: rows by `Bridge.prover_row`, masks
  by the CRT VOLE's correlation `Bridge.CrtComplete` (a hypothesis here, as for completeness;
  proved for `CrtGen.tables`, `Bridge.crtComplete`);
* the first accepted `H₂³` answer of the tape is the real grinding outcome (`firstHit_grind`).

Hypotheses (deterministic): `BAVCComplete`, `CrtComplete` for this run (proved:
`Bridge.bavcComplete`, and `Bridge.crtComplete` for `CrtGen.tables`; the two hypotheses of
`Bridge.verify_proveCommit`, checked by `lake exe prover_vectors`), and the hypotheses of
`qsProve_eq` (so that `Prover.qsProve` succeeds). `lake exe zk_sim` checks the equation itself on
all KAT runs.
-/

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.EndToEnd

/-- The hypotheses under which `Prover.qsProve` succeeds (part of `ZK/IdealSim.lean`'s `ZKHyp`). -/
structure ZKHypQ (st : Statement) (w : ByteArray) (cs : ByteArray → ByteArray → System GF128) :
    Prop where
  hvals : ∀ c1 lb x, st.values c1 lb x = (cs c1 lb).values x
  hdeg : ∀ c1 lb, ∀ e ∈ cs c1 lb, e.degree ≤ st.params.qsDegree
  hd : 1 ≤ st.params.qsDegree
  hd' : st.params.qsDegree + 1 < 2 ^ 64
  hsat : ∀ c1 lb, (cs c1 lb).Holds (wSlope st.params w)
  hw : w.size = st.params.witnessBytes
  hI : InterpOk st.params.qsDegree

/-! ## The real run -/

/-- The real `voleGen`'s fields that `voleGen_spec` leaves implicit. -/
lemma voleGen_more (Hs : Hashes) (T : CrtTables) (p : Params) (mu1 wPrefix rho binder1 : ByteArray) :
    let s := Prover.voleGen Hs T p mu1 wPrefix rho binder1
    let key := leafKey s.leaves
    let us : Array (Array UInt64) :=
      (Array.range BAVC.tau).map fun i => Prover.smallVoleUWords p s.iv i (key i)
    let cols := Prover.senderColumns p s.iv key
    let uPre : W128 := ⟨wordAt s.u p.labelRowOffset, wordAt s.u (p.labelRowOffset + 64)⟩
    s.seed = (Hs.hash .h3 ((wPrefix ++ mu1 ++ rho).push 3)).extract 0 16 ∧
    s.uMask = uMaskOfHi p T (AES.prg s.seed s.iv (((1 : UInt32) <<< 31) - 1) 0
      ((8 * p.nMask + 127) / 128)) us ∧
    s.fields.cmult = Prover.cMultOf p
      (gateWords ((Prover.gateInputsOff p T s.iv cols W128.zero).map (Hs.hash .h5)))
      (gateWords ((Prover.gateInputsOff p T s.iv cols uPre).map (Hs.hash .h5))) s.uMask ∧
    s.fields.opening = .empty ∧ s.fields.delta = .empty ∧ s.fields.ctr = .empty ∧
    s.u = us[0]! := by
  intro s key us cols uPre
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The real `proveCommit`, once QuickSilver has succeeded. -/
lemma proveCommit_eq (Hs : Hashes) (st : Statement) (s : Prover.Pending) (wSuffix w : ByteArray)
    (hp : s.params = st.params) (hw : s.wPrefix ++ wSuffix = w)
    (hws : w.size = st.params.witnessBytes)
    {check : GF128} {aT : Array GF128}
    (hq : Prover.qsProve
      { params := st.params, bytes := Prover.assemble st.params (realF1 st.params s w) }
      (realC2 Hs st s w) (st.values s.chal1 (st.combBytes Hs (realC2 Hs st s w)))
      s.vRows s.vMask s.uMask w = .ok (check, aT)) :
    Prover.proveCommit Hs st wSuffix s =
      match Prover.findFirst (Prover.grindStep Hs s
          (realC2 Hs st s w ++ gfToBytes check ++ Prover.gfsToBytes aT)) (2 ^ 32) 0 with
      | none => .error "grinding failed"
      | some (ctr, delta, opening) => .ok (Prover.assemble st.params
          { realF1 st.params s w with
            qsProof := Prover.gfsToBytes aT, opening := opening, delta := delta,
            ctr := AES.pushLE32 ByteArray.empty ctr.toUInt32 }) := by
  unfold Prover.proveCommit
  simp only [hp, hw, hws, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  simp only [realF1, realC2, realCorr] at hq ⊢
  rw [hq]
  simp only [bind, Except.bind]
  split
  · rename_i ctr delta opening hf
    rw [hf]; rfl
  · rename_i x hx
    cases h : Prover.findFirst _ (2 ^ 32) 0 with
    | none => rfl
    | some y => obtain ⟨a, b, c⟩ := y; exact absurd h (hx a b c)

/-! ## The ideal run, at the real values -/

/-- `idealTail` once its intermediate values are known. -/
lemma idealTail_of (Hs : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray) (sh : Shared)
    (ctr : ℕ) (delta : Bytes 16) (C M : ByteArray) (uM : Array W128) (ubits : Array Bool)
    (D : ByteArray) {c1 : ByteArray} {vR vM : Array W128} {ut : Array GF128} {hV : Array GF128}
    {F : Prover.Fields} {chk : GF128} {aT : Array GF128}
    (h1 : tC1 Hs st sh ctr delta C M = c1) (h2 : tVRows Hs T st sh delta C M ubits = vR)
    (h3 : tVMask Hs T st sh delta C M uM = vM) (h4 : tUt Hs st sh ctr delta C M ubits uM = ut)
    (h5 : voleHashReceiver st.params c1 vR vM 0 (Prover.zeros 64) = hV)
    (h6 : tF1 sh ctr delta C M ut D = F)
    (hq : Prover.qsProve { params := st.params, bytes := Prover.assemble st.params F }
      (chal2 Hs { params := st.params, bytes := Prover.assemble st.params F } c1 hV
        (st.muDelayed Hs c1) st.binder2)
      (st.values c1 (st.combBytes Hs (chal2 Hs
        { params := st.params, bytes := Prover.assemble st.params F } c1 hV (st.muDelayed Hs c1)
        st.binder2)))
      vR vM uM w = .ok (chk, aT)) :
    idealTail Hs T st w sh ctr delta C M uM ubits D =
      .ok (Prover.assemble st.params { F with
        qsProof := Prover.gfsToBytes aT, delta := ba delta, ctr := ctrBytes ctr,
        opening := (pubOf Hs st sh delta).opening }) := by
  simp only [idealTail]
  rw [h1, h2, h3, h4, h5, h6, hq]
  rfl

/-! ## The ideal run's values, at the real tape -/

section Values

variable (Hs : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray) (s : Prover.Pending)

/-- The real small VOLEs' inputs as words. -/
def realUsW (p : Params) (s : Prover.Pending) : Array (Array UInt64) :=
  (Array.range BAVC.tau).map fun i => Prover.smallVoleUWords p s.iv i (leafKey s.leaves i)

lemma smallVoleUWords_size (p : Params) (iv : ByteArray) (i : ℕ) (key : ℕ → ByteArray) :
    (Prover.smallVoleUWords p iv i key).size = p.colBytes / 8 :=
  (smallVoleUWords_spec p iv i key (r := 0) (by
    simp only [Params.colBytes, Params.voleColBlocks, Params.voleRows, Params.nMask]; omega)).1

lemma realUs_get (p : Params) {i : ℕ} (hi : i < BAVC.tau) :
    (realUs p s)[i]! = bytesOfWords (Prover.smallVoleUWords p s.iv i (leafKey s.leaves i)) := by
  rw [realUs, getElem!_range_map _ _ hi]

lemma realUs_size (p : Params) {i : ℕ} (hi : i < BAVC.tau) : ((realUs p s)[i]!).size = p.colBytes := by
  rw [realUs_get s p hi, bytesOfWords_size, smallVoleUWords_size]
  have := colBytes_mod8 p; omega

/-- **The tape's pads are the real small VOLEs' inputs.** -/
theorem usOf_realPads (p : Params) (delta : ByteArray) :
    usOf p (realPads Hs T p s delta) = realUsW p s := by
  let X : ℕ → ByteArray := fun i => if i < BAVC.tau then (realUs p s)[i]! else Prover.zeros p.colBytes
  have hX : ∀ i, (X i).size = p.colBytes := fun i => by
    simp only [X]; split_ifs with h
    · exact realUs_size s p h
    · exact zeros_size _
  have ht : realPads Hs T p s delta = (blk p.witnessBytes (X 0),
      blk (labelBytes p) ((X 0).extract p.witnessBytes p.correctionBytes),
      fun j => blk p.correctionBytes (X (j.val + 1)),
      fun j => blk p.nMask ((X j.val).extract p.correctionBytes (p.correctionBytes + p.nMask)),
      fun j => blk (restBytes p) ((X j.val).extract (p.correctionBytes + p.nMask) p.colBytes),
      (realPads Hs T p s delta).2.2.2.2.2.1, (realPads Hs T p s delta).2.2.2.2.2.2) := by
    have h0 : (0 : ℕ) < BAVC.tau := by decide
    have hj1 : ∀ j : Fin (BAVC.tau - 1), j.val + 1 < BAVC.tau := fun j => by
      have := j.isLt; have : BAVC.tau = 17 := rfl; omega
    simp only [realPads, padsOfArrays, X, h0, ↓reduceIte, hj1, Fin.is_lt]
  apply Array.ext
  · simp [usOf, realUsW]
  intro i h1 h2
  have hi : i < BAVC.tau := by simpa [usOf] using h1
  rw [← getElem!_pos _ i h1, ← getElem!_pos _ i h2, usOf_get _ hi, ht,
    usBytes_reassemble p X hX _ _ hi]
  simp only [X, hi, ↓reduceIte, realUs_get s p hi, wordsOf_bytesOfWords, realUsW,
    getElem!_range_map _ _ hi]

lemma correctionsOf_real (p : Params)
    (hscorr : s.fields.corrections = (List.range (BAVC.tau - 1)).foldl
      (fun acc j => acc ++ proverCorr p s.iv (leafKey s.leaves) (j + 1)) ByteArray.empty) :
    correctionsOf p (realUsW p s) = s.fields.corrections := by
  rw [hscorr, correctionsOf]
  refine List.foldl_ext _ _ _ fun acc j hj => ?_
  have hj := List.mem_range.1 hj
  have h17 : BAVC.tau = 17 := rfl
  simp only [realUsW, proverCorr, proverU, getElem!_range_map _ _ (show 0 < BAVC.tau by decide),
    getElem!_range_map _ _ (show j + 1 < BAVC.tau by omega)]

lemma realUsW_zero (p : Params) (hsu : s.u = proverU p s.iv (leafKey s.leaves) 0) :
    (realUsW p s)[0]! = s.u := by
  rw [realUsW, getElem!_range_map _ _ (show 0 < BAVC.tau by decide), hsu]; rfl

lemma uMask_real (p : Params) (hi : ByteArray)
    (huMask : s.uMask = uMaskOfHi p T hi ((Array.range BAVC.tau).map fun i =>
      Prover.smallVoleUWords p s.iv i (leafKey s.leaves i))) :
    uMaskOfHi p T (ba (blk p.nMask hi)) (realUsW p s) = s.uMask := by
  rw [huMask]
  refine Array.map_congr_left fun m hm => ?_
  have hm := Array.mem_range.1 hm
  rw [get!_ba _ hm, get_blk]
  rfl

lemma size_foldl_range (f : ℕ → ByteArray) (m : ℕ) :
    ∀ n, (∀ i < n, (f i).size = m) → ∀ acc : ByteArray,
      ((List.range n).foldl (fun acc i => acc ++ f i) acc).size = acc.size + m * n
  | 0, _, acc => by simp
  | n + 1, hf, acc => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ByteArray.size_append,
      size_foldl_range f m n (fun i hi => hf i (by omega)) acc, hf n (by omega), Nat.mul_succ,
      Nat.add_assoc]

/-- `openingOf` has `OPEN_SIZE` bytes when the opening fits. -/
lemma openingOf_size (delta : ByteArray) (coms : Fin BAVC.tau → Bytes 32)
    (seeds : Fin 105 → Bytes 16) (h : openCount delta ≤ 105) :
    (openingOf delta coms seeds).size = BAVC.openSize := by
  have h1 := size_foldl_range (fun i => if h : i < BAVC.tau then ba (coms ⟨i, h⟩)
    else ByteArray.empty) 32 BAVC.tau (fun i hi => by simp [hi]) ByteArray.empty
  have h2 := size_foldl_range (fun k => if h : k < 105 then ba (seeds ⟨k, h⟩)
    else ByteArray.empty) 16 (openCount delta) (fun k hk => by simp [show k < 105 by omega])
  simp only [openingOf, ByteArray.size_append, zeros_size, h2, h1, ByteArray.size_empty]
  have e1 : BAVC.openSize = 32 * 17 + 105 * 16 := rfl
  have e2 : BAVC.tau = 17 := rfl
  omega

/-! ### The prover's tags on the label rows -/

lemma convertToVoleAt_col_size (p : Params) (dbit : ℕ → Bool) (corr : ℕ → ByteArray)
    (iv : ByteArray) (key : ℕ → ℕ → ByteArray) {c : ℕ} (hc : c < 120) :
    p.colBytes / 8 ≤ ((convertToVoleAt p dbit corr iv key)[c]!).size := by
  obtain ⟨hi, hle, hb⟩ := treeOf_spec hc
  have hcc : c = BAVC.bitOffset (BAVC.treeOf c) + (c - BAVC.bitOffset (BAVC.treeOf c)) := by omega
  rw [hcc, convertToVoleAt_col _ _ _ _ _ hi hb]
  unfold treeColumns
  rw [getElem!_range_map _ _ hb]
  have hpos : 0 < p.colBytes / 8 := by
    simp only [Params.colBytes, Params.voleColBlocks, Params.voleRows, Params.nMask]; omega
  have hacc : 0 / 64 < (if (BAVC.hiddenIndex dbit (BAVC.treeOf c)).testBit
      (c - BAVC.bitOffset (BAVC.treeOf c)) then corrWords p (BAVC.treeOf c) (corr (BAVC.treeOf c))
      else zeroCol p).size := by
    have := corrWords_size p (BAVC.treeOf c) (corr (BAVC.treeOf c))
    split <;> simp [zeroCol] <;> omega
  rw [(foldl_xor_bit _ _ _ _ hacc).1]
  have := corrWords_size p (BAVC.treeOf c) (corr (BAVC.treeOf c))
  split <;> simp [zeroCol]; omega

/-- **The prover's tags as `q + Δ·u`** agree with its own tag columns on the corrected rows. -/
lemma wbit_tagCols (p : Params) (dbit : ℕ → Bool) (iv : ByteArray) (key : ℕ → ℕ → ByteArray)
    {c r : ℕ} (hc : c < 120) (hr : r < p.correctionRows) :
    wbit (tagCols dbit (convertToVoleAt p dbit (proverCorr p iv key) iv key)
      (proverU p iv key 0))[c]! r = wbit (Prover.senderColumns p iv key)[c]! r := by
  obtain ⟨hi, hle, hb⟩ := treeOf_spec hc
  have hcc : c = BAVC.bitOffset (BAVC.treeOf c) + (c - BAVC.bitOffset (BAVC.treeOf c)) := by omega
  have hcol := prover_column p iv key dbit hi hb hr
  rw [← hcc] at hcol
  rw [tagCols, getElem!_range_map _ _ (by omega)]
  have hsz := convertToVoleAt_col_size p dbit (proverCorr p iv key) iv key hc
  have hrl := correctionRows_lt p
  split_ifs with hd
  · rw [wbit_xorWords _ _ (by omega), hcol, hd]
    cases wbit (Prover.senderColumns p iv key)[c]! r <;> cases wbit (proverU p iv key 0) r <;> rfl
  · rw [hcol]; simp [hd]

lemma gateInputsOff_length (p : Params) (T : CrtTables) (iv : ByteArray)
    (cols : Array (Array UInt64)) (off : W128) : (Prover.gateInputsOff p T iv cols off).length = 312 := by
  simp [Prover.gateInputsOff, Params.nMult]

/-- The ideal gate hashes with the real run's sibling answers are the real gate hashes. -/
lemma gateHashesIdeal_real (Hs : Hashes) (hHs : HashesWF Hs) (gamma : Array UInt64)
    (in0 in1 : List ByteArray) (hl0 : in0.length = 312) (hl1 : in1.length = 312) (b : Bool) :
    gateHashesIdeal Hs gamma b (if b then in1 else in0)
      (fun e => blk 4 (sibAnswers Hs gamma in0 in1)[e.val]!) =
      gateWords ((if b then in1 else in0).map (Hs.hash .h5)) := by
  have hl : (if b then in1 else in0).length = 312 := by cases b <;> simpa
  apply Array.ext
  · simp [gateHashesIdeal, gateWords, hl]
  intro e h1 h2
  have he : e < 312 := by simpa [gateHashesIdeal, gateWords] using h1
  rw [← getElem!_pos _ e h1, ← getElem!_pos _ e h2, gateHashesIdeal_get _ _ _ _ _ he,
    gateWords_get _ (by simpa [hl] using he)]
  simp only [List.getElem_map]
  have hsib : (sibAnswers Hs gamma in0 in1)[e]! =
      Hs.hash .h5 ((if wbit gamma e then in0 else in1).getD e ByteArray.empty) := by
    rw [sibAnswers, getElem!_range_map _ _ he]
  rw [hsib, ba_blk_of_size (n := 4) (hHs .h5 _)]
  cases b <;> cases hgb : wbit gamma e <;>
    simp [hl0, hl1, he]

end Values

/-! ## The tape of a step-1 state -/

/-- The tape of a real step 1 `s` with the grinding answers `g`: `iv_pre`, `g`, the hidden
commitments and the opened seeds at the first accepted `Δ` of `g` (zero if there is none), and
`realPads`. `tapeOf` is this at the run's own grinding answers. -/
def tapeAt (Hs : Hashes) (T : CrtTables) (p : Params) (s : Prover.Pending)
    (g : Fin nGrind → Bytes 16) : IdealTape p :=
  let delta := ba ((firstHit g).map (·.2) |>.getD fun _ => 0)
  ((blk 16 s.ivPre, g, comsOf s.leaves.coms delta, seedsOf s.tree delta), realPads Hs T p s delta)

lemma tapeOf_eq_tapeAt (Hs : Hashes) (T : CrtTables) (st : Statement) (w rho : ByteArray)
    (k : ℕ) :
    tapeOf Hs T st w rho k = tapeAt Hs T st.params
      (Prover.voleGen Hs T st.params (st.mu1 Hs) (w.extract 0 k) rho st.binder1)
      (realGrind Hs (realPre Hs st
        (Prover.voleGen Hs T st.params (st.mu1 Hs) (w.extract 0 k) rho st.binder1) w)) := rfl

/-! ## Step 1 -/

/-- **The ideal run's step-1 values at the tape of a real step 1**, at any `Δ` whose opening fits
(`BAVC.openAt` succeeds): the pads are the small VOLEs' inputs, the public values (`iv`, the
opening) and the verifier's key columns are the real ones, and so are `c_mult`, `chal1` and the
VOLE check `ũ`. -/
theorem step1_real (Hs : Hashes) (T : CrtTables) (st : Statement) (s : Prover.Pending)
    {wPrefix rho : ByteArray}
    (hs : Prover.voleGen Hs T st.params (st.mu1 Hs) wPrefix rho st.binder1 = s)
    (hHs : HashesWF Hs) (hbavc : BAVCComplete)
    (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    (g : Fin nGrind → Bytes 16) (ctr : ℕ) {delta opening : ByteArray} (hd16 : delta.size = 16)
    (hopen : BAVC.openAt s.tree s.leaves.coms delta = some opening) :
    let sh : Shared := (blk 16 s.ivPre, g, comsOf s.leaves.coms delta, seedsOf s.tree delta)
    let t := realPads Hs T st.params s delta
    let P := pubOf Hs st sh (blk 16 delta)
    let key := leafKey s.leaves
    let qcols := convertToVoleAt st.params (BAVC.deltaBit delta) (proverCorr st.params s.iv key)
      s.iv key
    usOf st.params t = realUsW st.params s ∧ (realUsW st.params s)[0]! = s.u ∧
    correctionsOf st.params (realUsW st.params s) = s.fields.corrections ∧
    uMaskOfHi st.params T (ba t.2.2.2.2.2.1) (realUsW st.params s) = s.uMask ∧
    P.iv = s.iv ∧ P.opening = opening ∧
    qcolsOf st P (blk 16 delta) s.fields.corrections = qcols ∧
    cmultIdeal Hs T st P (blk 16 delta) qcols s.u s.uMask t.2.2.2.2.2.2 = s.fields.cmult ∧
    tC1 Hs st sh ctr (blk 16 delta) s.fields.corrections s.fields.cmult = s.chal1 ∧
    tUt Hs st sh ctr (blk 16 delta) s.fields.corrections s.fields.cmult
        ((Array.range st.params.correctionRows).map (wbit s.u)) s.uMask =
      voleHashReceiver st.params s.chal1 ((Array.range st.params.correctionRows).map fun r =>
        if wbit s.u r then (⟨1, 0⟩ : W128) else W128.zero) s.uMask 0 (Prover.zeros 64) := by
  intro sh t P key qcols
  have spec := voleGen_spec Hs T st.params (st.mu1 Hs) wPrefix rho st.binder1
  have more := voleGen_more Hs T st.params (st.mu1 Hs) wPrefix rho st.binder1
  rw [hs] at spec more
  obtain ⟨hsp, hsw, hsiv, hsivp, hstree, hsleaves, hsu, hscorr, hsfiv, hsqs, hsvrows, hsvs, hsvm,
    hsum, hsc1, hsvc, hshv⟩ := spec
  obtain ⟨hseed, huMask, hcm, hsop, hsdl, hsct, hsu0⟩ := more
  have hivs : s.ivPre.size = 16 := by rw [hsivp, ByteArray.size_extract, hHs]; rfl
  have hseeds : s.seed.size = 16 := by rw [hseed, ByteArray.size_extract, hHs]; rfl
  have hcs : s.leaves.coms.size = BAVC.hashLen * BAVC.numLeaves := by
    rw [hsleaves]; exact commit_coms_size _ _
  have htree : ∀ k < BAVC.numNodes, (s.tree[k]!).size = 16 := by
    rw [hstree]; exact (expandTree_spec _ _ hseeds).2
  have hopen' : openingOf delta (comsOf s.leaves.coms delta) (seedsOf s.tree delta) = opening := by
    have := openingOf_eq s.tree s.leaves.coms delta hd16 hcs htree hopen
    rwa [ba_blk_of_size hd16] at this
  have hcount : openCount delta ≤ 105 := by
    have ho := openAt_isSome s.tree s.leaves.coms delta
    rw [hopen] at ho; simpa using ho
  have hosz : opening.size = BAVC.openSize := by
    rw [← hopen']; exact openingOf_size _ _ _ hcount
  obtain ⟨leavesR, hrec, hcoms, hkeys⟩ := hbavc s.seed s.iv delta opening
    (by rw [← hstree, ← hsleaves]; exact hopen)
  rw [fit_of_size hosz] at hrec
  rw [← hsleaves] at hcoms hkeys
  -- The public values.
  have hPiv : P.iv = s.iv := by
    simp only [P, pubOf, sh, ba_blk_of_size hivs]; exact hsiv.symm
  have hPop : P.opening = opening := by
    simp only [P, pubOf, sh, ba_blk_of_size hd16]; exact hopen'
  have hPleaves : P.leaves = leavesR := by
    have : P.leaves = (BAVC.reconstruct P.iv P.opening (ba (blk 16 delta))).getD ⟨.empty, .empty⟩ :=
      rfl
    rw [this, hPiv, hPop, ba_blk_of_size hd16, hrec]; rfl
  have hPcheck : P.check = BAVC.check (Hs.hash .h1) s.leaves.coms := by
    have : P.check = BAVC.check (Hs.hash .h1) P.leaves.coms := rfl
    rw [this, hPleaves, hcoms]
  have hPmu : P.mu1 = st.mu1 Hs := rfl
  -- The verifier's key columns.
  have hcsz : ∀ i, (proverCorr st.params s.iv key i).size = st.params.correctionBytes := fun i =>
    correctionOf_size _ _ _ (by rw [proverU, smallVoleUWords_size])
  have hqcols : qcolsOf st P (blk 16 delta) s.fields.corrections = qcols := by
    unfold qcolsOf
    rw [hPiv, hPleaves, ba_blk_of_size hd16,
      convertToVoleAt_congr_key st.params _ _ s.iv (key' := key)
        fun i hi j hj hjd => hkeys i hi j hj hjd]
    refine convertToVoleAt_congr_corr st.params _ s.iv key fun i hi1 hi => ?_
    rw [hscorr]
    exact correctionOf_concat st.params (proverCorr st.params s.iv key) hcsz hi1 hi
  -- `c_mult`.
  have hcmI : cmultIdeal Hs T st P (blk 16 delta) qcols s.u s.uMask t.2.2.2.2.2.2 =
      s.fields.cmult := by
    unfold cmultIdeal
    dsimp only
    rw [ba_blk_of_size hd16, hPiv]
    have hcongr : ∀ off, Prover.gateInputsOff st.params T s.iv
        (tagCols (BAVC.deltaBit delta) qcols s.u) off =
        Prover.gateInputsOff st.params T s.iv (Prover.senderColumns st.params s.iv key) off :=
      fun off => gateInputsOff_congr _ _ _ off fun c hc k hk => by
        rw [hsu]; exact wbit_tagCols _ _ _ _ hc (by omega)
    rw [hcongr, hcongr]
    have hf := gateHashesIdeal_real Hs hHs (gammaOf T (BAVC.deltaBit delta))
      (Prover.gateInputsOff st.params T s.iv (Prover.senderColumns st.params s.iv key) W128.zero)
      (Prover.gateInputsOff st.params T s.iv (Prover.senderColumns st.params s.iv key)
        ⟨wordAt s.u st.params.labelRowOffset, wordAt s.u (st.params.labelRowOffset + 64)⟩)
      (gateInputsOff_length _ _ _ _ _) (gateInputsOff_length _ _ _ _ _)
    have hf0 := hf false
    have hf1 := hf true
    simp only [Bool.false_eq_true, ↓reduceIte] at hf0 hf1
    have hsib : t.2.2.2.2.2.2 = fun e =>
        blk 4 (sibAnswers Hs (gammaOf T (BAVC.deltaBit delta))
          (Prover.gateInputsOff st.params T s.iv (Prover.senderColumns st.params s.iv key) W128.zero)
          (Prover.gateInputsOff st.params T s.iv (Prover.senderColumns st.params s.iv key)
            ⟨wordAt s.u st.params.labelRowOffset, wordAt s.u (st.params.labelRowOffset + 64)⟩))[e.val]! :=
      rfl
    rw [hsib, hf0, hf1, hcm]
  -- `chal1` and `ũ`.
  have hF0 : tF0 sh ctr (blk 16 delta) s.fields.corrections s.fields.cmult =
      { s.fields with voleCheck := .empty, correction := .empty } := by
    simp only [tF0, publicFields, sh, ba_blk_of_size hivs, hsqs, hsop, hsdl, hsct, hsfiv]
  have h1 : tC1 Hs st sh ctr (blk 16 delta) s.fields.corrections s.fields.cmult = s.chal1 := by
    unfold tC1
    dsimp only
    rw [show pubOf Hs st sh (blk 16 delta) = P from rfl, hPcheck, hF0, hsc1, hPmu]
    rfl
  have h4 : tUt Hs st sh ctr (blk 16 delta) s.fields.corrections s.fields.cmult
      ((Array.range st.params.correctionRows).map (wbit s.u)) s.uMask =
      voleHashReceiver st.params s.chal1 ((Array.range st.params.correctionRows).map fun r =>
        if wbit s.u r then (⟨1, 0⟩ : W128) else W128.zero) s.uMask 0 (Prover.zeros 64) := by
    have hur : tURows st ((Array.range st.params.correctionRows).map (wbit s.u)) =
        (Array.range st.params.correctionRows).map fun r =>
          if wbit s.u r then (⟨1, 0⟩ : W128) else W128.zero :=
      Array.map_congr_left fun r hr => by rw [getElem!_range_map _ _ (Array.mem_range.1 hr)]
    unfold tUt
    rw [h1, hur]
  have hhi : t.2.2.2.2.2.1 = blk st.params.nMask
      (AES.prg s.seed s.iv (((1 : UInt32) <<< 31) - 1) 0 ((8 * st.params.nMask + 127) / 128)) :=
    rfl
  refine ⟨usOf_realPads Hs T s _ _, realUsW_zero s _ hsu, correctionsOf_real s _ hscorr, ?_, hPiv,
    hPop, hqcols, hcmI, h1, h4⟩
  rw [hhi]
  exact uMask_real T s _ _ huMask

/-! ## The main theorem -/

/-- **Step 2 of a real run is the ideal-tape prover at the run's tape**, for any split of the
witness `wPrefix ++ wSuffix` between the steps (`Prover.prove` passes the whole witness to step 1;
PomFRIT passes `r`). -/
theorem proveCommit_eq_proveIdeal (Hs : Hashes) (T : CrtTables) (st : Statement)
    (wPrefix wSuffix rho : ByteArray)
    (cs : ByteArray → ByteArray → System GF128) (h : ZKHypQ st (wPrefix ++ wSuffix) cs)
    (hHs : HashesWF Hs) (hbavc : BAVCComplete)
    (hcrt : CrtComplete (Hs.hash .h5) T (Prover.voleGen Hs T st.params (st.mu1 Hs) wPrefix rho
      st.binder1))
    (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows) :
    let s := Prover.voleGen Hs T st.params (st.mu1 Hs) wPrefix rho st.binder1
    Prover.proveCommit Hs st wSuffix s = proveIdeal Hs T st (wPrefix ++ wSuffix)
      (tapeAt Hs T st.params s (realGrind Hs (realPre Hs st s (wPrefix ++ wSuffix)))) := by
  intro s
  have hs : Prover.voleGen Hs T st.params (st.mu1 Hs) wPrefix rho st.binder1 = s := rfl
  set w := wPrefix ++ wSuffix with hwdef
  have spec := voleGen_spec Hs T st.params (st.mu1 Hs) wPrefix rho st.binder1
  rw [hs] at spec hcrt
  clear_value s
  obtain ⟨hsp, hsw, hsiv, hsivp, hstree, hsleaves, hsu, hscorr, hsfiv, hsqs, hsvrows, hsvs, hsvm,
    hsum, hsc1, hsvc, hshv⟩ := spec
  -- QuickSilver succeeds.
  have h0 : ∀ i, gfOfBytes (Proof.mk st.params (Prover.assemble st.params
      (realF1 st.params s w))).qsProof (16 * i) = 0 := by
    intro i
    rw [(fields_assemble st.params _).2.2.2.2.1]
    show gfOfBytes (Prover.fit s.fields.qsProof _) _ = 0
    rw [hsqs, fit_empty, gfOfBytes_zeros]
  have hq := qsProve_eq (Proof.mk st.params (Prover.assemble st.params (realF1 st.params s w)))
    (realC2 Hs st s w) (st.values s.chal1 (st.combBytes Hs (realC2 Hs st s w))) s.vRows s.vMask
    s.uMask w (cs s.chal1 (st.combBytes Hs (realC2 Hs st s w))) (h.hvals _ _) (h.hdeg _ _) h.hd
    h.hd' h0 h.hI (h.hsat _ _)
  rw [proveCommit_eq Hs st s wSuffix w hsp (by rw [hsw]) h.hw hq]
  have hpreq : realPre Hs st s w = realC2 Hs st s w ++
      gfToBytes ((qsPoly st.params (realC2 Hs st s w)
        (cs s.chal1 (st.combBytes Hs (realC2 Hs st s w))) s.vRows s.vMask s.uMask w).coeff 0) ++
      Prover.gfsToBytes ((Array.range (st.params.qsDegree - 1)).map fun i =>
        (qsPoly st.params (realC2 Hs st s w) (cs s.chal1 (st.combBytes Hs (realC2 Hs st s w)))
          s.vRows s.vMask s.uMask w).coeff (i + 1)) := by
    rw [realPre, hq]
  rw [hpreq]
  unfold proveIdeal tapeAt
  simp only [h.hw, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  generalize realC2 Hs st s w ++ _ ++ _ = pre
  have hfh : (firstHit (realGrind Hs pre)).map (fun x => (x.1, ba x.2)) =
      (Prover.findFirst (Prover.grindStep Hs s pre) (2 ^ 32) 0).map fun x => (x.1, x.2.1) :=
    firstHit_grind Hs hHs s pre
  rcases hff : Prover.findFirst (Prover.grindStep Hs s pre) (2 ^ 32) 0 with _ | ⟨ctr, delta, opening⟩
  · rw [hff] at hfh
    have : firstHit (realGrind Hs pre) = none := by simpa using hfh
    rw [this]
  · rw [hff] at hfh
    obtain ⟨⟨ctr', d'⟩, hfd, heq⟩ := Option.map_eq_some_iff.1 hfh
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, hd'⟩ := heq
    obtain ⟨k, hk⟩ := findFirst_some _ _ _ hff
    obtain ⟨-, hdelta, h15, hopen⟩ := grindStep_some hk
    have hd16 : delta.size = 16 := by rw [hdelta]; exact hHs _ _
    have hd'' : d' = blk 16 delta := by
      rw [← hd']; funext i; rw [get_blk, get!_ba _ i.isLt]
    subst hd''
    rw [hfd]
    simp only [Option.map_some, Option.getD_some, ba_blk_of_size hd16]
    obtain ⟨hus, hu0, hcorr, huM, hPiv, hPop, hqcols, hcmI, h1, h4⟩ :=
      step1_real Hs T st s hs hHs hbavc hlab (realGrind Hs pre) ctr' hd16 hopen
    set key := leafKey s.leaves with hkey
    set sh : Shared := (blk 16 s.ivPre, realGrind Hs pre, comsOf s.leaves.coms delta,
      seedsOf s.tree delta) with hsh
    -- The ideal run's inputs are the real ones.
    unfold idealCore
    dsimp only
    rw [hus, hu0, hcorr, huM, hqcols, hcmI]
    -- The verifier's recomputation is the real run's.
    have hcrtE : tCrt Hs T st sh (blk 16 delta) s.fields.corrections s.fields.cmult =
        crtReconstructAt (Hs.hash .h5) st.params (BAVC.deltaBit delta)
          (Prover.fit s.fields.cmult (st.params.nMask * st.params.nMultBytes)) T s.iv
          (convertToVoleAt st.params (BAVC.deltaBit delta) (proverCorr st.params s.iv key) s.iv
            key) := by
      unfold tCrt
      rw [ba_blk_of_size hd16, hPiv, hqcols]
    have hdl : tDL T (blk 16 delta) = (W128.rowMul (BAVC.deltaBit delta) 120 T.wCrt).toGF := by
      unfold tDL; rw [ba_blk_of_size hd16]
    have h2c : ∀ y : GF128, y + y = 0 := fun y => CharTwo.add_self_eq_zero y
    have hF0 : tF0 sh ctr' (blk 16 delta) s.fields.corrections s.fields.cmult =
        { s.fields with voleCheck := .empty, correction := .empty } := by
      have hivs : s.ivPre.size = 16 := by rw [hsivp, ByteArray.size_extract, hHs]; rfl
      have more := voleGen_more Hs T st.params (st.mu1 Hs) wPrefix rho st.binder1
      rw [hs] at more
      obtain ⟨-, -, -, hsop, hsdl, hsct, -⟩ := more
      simp only [tF0, publicFields, hsh, ba_blk_of_size hivs, hsqs, hsop, hsdl, hsct, hsfiv]
    have h2 : tVRows Hs T st sh (blk 16 delta) s.fields.corrections s.fields.cmult
        ((Array.range st.params.correctionRows).map (wbit s.u)) = s.vRows := by
      unfold tVRows
      dsimp only
      rw [hcrtE, hdl]
      apply Array.ext
      · simp [hsvs]
      intro r hr1 hr2
      have hr : r < st.params.correctionRows := by simpa using hr1
      rw [← getElem!_pos _ r hr1, ← getElem!_pos _ r hr2, getElem!_range_map _ _ hr,
        getElem!_range_map _ _ hr, prover_row _ (gateWords ((Prover.gateInputsOff st.params T s.iv
          (Prover.senderColumns st.params s.iv key) W128.zero).map (Hs.hash .h5))) _ _ _
          ByteArray.empty _ _ _ hr, ← hsvrows, ← hsu]
      show Prover.W128.ofGF (s.vRows[r]!.toGF + _ * _ + _) = _
      cases wbit s.u r
      · simp only [Bool.false_eq_true, ↓reduceIte, zero_mul, add_zero]; rfl
      · simp only [↓reduceIte, one_mul, add_assoc, h2c, add_zero]; rfl
    have h3 : tVMask Hs T st sh (blk 16 delta) s.fields.corrections s.fields.cmult s.uMask =
        s.vMask := by
      unfold tVMask
      dsimp only
      rw [hcrtE, hdl]
      apply Array.ext
      · simp [hsvm]
      intro m hm1 hm2
      have hm : m < st.params.nMask := by simpa using hm1
      rw [← getElem!_pos _ m hm1, ← getElem!_pos _ m hm2, getElem!_range_map _ _ hm]
      have hc := hcrt (BAVC.deltaBit delta) m (by rw [hsp]; exact hm)
      rw [hsp, ← hkey] at hc
      rw [hc, add_assoc, h2c, add_zero]
      rfl
    have h6 : tF1 sh ctr' (blk 16 delta) s.fields.corrections s.fields.cmult
        (voleHashReceiver st.params s.chal1 ((Array.range st.params.correctionRows).map fun r =>
          if wbit s.u r then (⟨1, 0⟩ : W128) else W128.zero) s.uMask 0 (Prover.zeros 64))
        (realCorr st.params s w) = realF1 st.params s w := by
      simp only [tF1, hF0, realF1, ← hsvc]
    have hq' : Prover.qsProve
        { params := st.params, bytes := Prover.assemble st.params (realF1 st.params s w) }
        (chal2 Hs { params := st.params, bytes := Prover.assemble st.params (realF1 st.params s w) }
          s.chal1 s.hV (st.muDelayed Hs s.chal1) st.binder2)
        (st.values s.chal1 (st.combBytes Hs (chal2 Hs
          { params := st.params, bytes := Prover.assemble st.params (realF1 st.params s w) }
          s.chal1 s.hV (st.muDelayed Hs s.chal1) st.binder2)))
        s.vRows s.vMask s.uMask w = _ := hq
    change _ = idealTail Hs T st w sh ctr' (blk 16 delta) s.fields.corrections s.fields.cmult s.uMask
      ((Array.range st.params.correctionRows).map (wbit s.u)) (realCorr st.params s w)
    rw [idealTail_of Hs T st w sh ctr' (blk 16 delta) _ _ _ _ _ h1 h2 h3 h4 hshv.symm h6 hq',
      hPop, ba_blk_of_size hd16]
    rfl

theorem prove_eq_proveIdeal (Hs : Hashes) (T : CrtTables) (st : Statement) (w rho : ByteArray)
    (cs : ByteArray → ByteArray → System GF128) (h : ZKHypQ st w cs)
    (hHs : HashesWF Hs) (hbavc : BAVCComplete)
    (hcrt : CrtComplete (Hs.hash .h5) T (Prover.voleGen Hs T st.params (st.mu1 Hs)
      (w.extract 0 st.params.witnessBytes) rho st.binder1))
    (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows) :
    Prover.prove Hs T st w rho = proveIdeal Hs T st w (tapeOf Hs T st w rho) := by
  have hpre : w.extract 0 st.params.witnessBytes = w := by
    rw [← h.hw, ByteArray.extract_zero_size]
  have hsuf : w.extract st.params.witnessBytes w.size = ByteArray.empty := by
    rw [h.hw, ByteArray.extract_eq_empty_iff]; omega
  have hw : w.extract 0 st.params.witnessBytes ++ w.extract st.params.witnessBytes w.size = w := by
    rw [hpre, hsuf, ByteArray.append_empty]
  have e := proveCommit_eq_proveIdeal Hs T st (w.extract 0 st.params.witnessBytes)
    (w.extract st.params.witnessBytes w.size) rho cs (by rw [hw]; exact h) hHs hbavc hcrt hlab
  rw [hw] at e
  exact e

end VoleMole.ZK.Sim
