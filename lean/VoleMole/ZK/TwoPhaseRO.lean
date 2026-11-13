import VoleMole.ZK.TwoPhaseHops
import VoleMole.ZK.HopsH23

/-!
# Two-phase zero knowledge with the tables visible: the hybrids around H4 (`lean/docs/zk.md` §10.1)

`ZK/HopsH23.lean` proves zero knowledge of the single-phase prover against a distinguisher that
sees the `H₃`, `H₂³` and `H₅` tables, the simulator programming `H₂³`. Here the same for the
two-phase prover of `ZK/TwoPhase.lean` (PomFRIT: step 1 with the witness prefix `r`, then the
continuation `k` picks the instance and the witness suffix from step 1's output, then step 2), for
any CTR PRG (`HasPrg`). `ZK/TwoPhaseIC.lean` adds H4 in the ideal-cipher model and composes.

**The model.** The record is `recH Hb (st1 st) r G3 G2 G5` (`H₃` a table at step 1's seed inputs
`r ‖ μ₁ ‖ ρ ‖ 3`, `H₂³` at every grinding point, `H₅` at every 37-byte input). The continuation
may depend on the `H₅` table (`kf G5`; not on `H₃` or `H₂³`): in PomFRIT's blindness game it is the
Client's `hash_to_target` and the Issuer's response, which depends on the other session's request,
which reads the tables. The steps that vary `H₅` (H6) pay for its reads; the others fix it.
(`ZK/TwoPhaseIC.lean` lets it depend on the cipher too.)

**The simulator** outputs `simRun2 Hb …` (from its coins only: step 1's fields uniform with the
verifier's `chal1`, step 2's proof `simulate`'s, a fallback block when no grinding answer is
accepted) and programs `H₂³` (`simTab2`) at the grinding points of the prefix it recomputes from
its final proof with the verifier's `vPre` **for the instance the continuation picks from its
step-1 output** (`outPre2`; nothing is programmed at a meaningful point if the continuation stops).

**The hybrids.**
* `real_form` (no probability): the real run is `hyb2'` at `H₃`'s answer and the `H₂³` table's
  answers at the grinding points of `preP` (the prefix of the instance picked, or the empty prefix
  if the continuation stops: then the run does not read the grinding answers, `hyb2'_none`).
* `zk2_h1` (H1, `≤ q₃·2⁻¹²⁸`), `zk2_prog` (programming, exact), `zk2_keys` (`≤ Pr[GrindBad]`):
  the programmed points switched to the recomputed ones **and the fallback block to a uniform
  one**, at once; outside `GrindBad` an answer is accepted, so the fallback block is not read
  (`proveIdeal2_fb`), and the run is a real two-phase run for a record built for it
  (`realRun2_recAt2`), on which the verifier recomputes the prover's prefix
  (`hyb2'_vPre`, from `vPre_proveCommit`). So the abort term `noHitProb` of `tapeHyp2_of_hops` is
  inside `Pr[GrindBad]` here.
* After H4: `zk2_tape` (exact), `zk2_h6` (`≤ (q₅ + q_k5 + 1)·2⁻¹²⁸`, `q_k5` the continuation's
  `H₅` reads: `lab_romG` with the two-phase bad
  event `pr_bad2`, whose guesses are functions of the shared tape and the adaptive fields
  `fieldsAd`, independent of `Θ` by `upush_fieldsAdθ`), `zk2_sim` (exact, `proveIdeal2_close_at`).
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

-- The statements hold for any CTR PRG (`HasPrg`, `Verifier/Prg.lean`), AES included.
variable [VoleMole.Verifier.HasPrg]
set_option linter.unusedSectionVars false

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy

/-! ## The two-phase run does not read `H₃` or `H₂³` -/

section Congr2

variable {kd : Kind} {Hs Hs' : Hashes} (hu : Unread kd) (h : Hs.AgreeOff kd Hs')
  (T : CrtTables) (st : Statement) (r : ByteArray) (k : Cont2)
include hu h

lemma idealPhase1_agreeOff : idealPhase1 Hs T st r = idealPhase1 Hs' T st r := by
  have hP := h.pubOf' hu st
  have h5 := h .h5 (Ne.symm hu.2.2.2.2.2.2.1)
  have hc1 := h.chal1 hu.2.2.2.2.1
  funext s ctr d t
  simp only [idealPhase1, cmultIdeal, gateHashesIdeal, tUt, tC1, hP, h5, hc1]

lemma idealCore_agreeOff (w : ByteArray) : idealCore Hs T st w = idealCore Hs' T st w := by
  have hP := h.pubOf' hu st
  have h5 := h .h5 (Ne.symm hu.2.2.2.2.2.2.1)
  have hc1 := h.chal1 hu.2.2.2.2.1
  have hc2 := h.chal2 hu.2.2.2.2.2.1
  have hmd := h.muDelayed hu.1 st
  have hcb := h.combBytes hu.2.2.2.2.2.2.2 st
  funext s ctr d t
  simp only [idealCore, idealTail, cmultIdeal, gateHashesIdeal, tCrt, tVRows, tVMask,
    tUt, tC1, hP, h5, hc1, hc2, hmd, hcb]

theorem proveIdeal2_agreeOff : proveIdeal2 Hs T st r k = proveIdeal2 Hs' T st r k := by
  funext t
  simp only [proveIdeal2, idealPhase1_agreeOff hu h T, idealCore_agreeOff hu h T]

lemma realPre_agreeOff (st' : Statement) (s : Prover.Pending) (w : ByteArray) :
    realPre Hs st' s w = realPre Hs' st' s w := by
  simp only [realPre, realC2, h.chal2 hu.2.2.2.2.2.1, h.muDelayed hu.1 st',
    h.combBytes hu.2.2.2.2.2.2.2 st']

lemma pre2_agreeOff : pre2 Hs T st r k = pre2 Hs' T st r k := by
  funext x
  simp only [pre2, pendAt_agreeOff hu h T (st1 st), realPre_agreeOff hu h]

lemma fb2_agreeOff : fb2 Hs T st r = fb2 Hs' T st r := by
  funext x
  simp only [fb2, pendAt_agreeOff hu h T (st1 st)]

lemma tapeAt_agreeOff (p : Params) : tapeAt Hs T p = tapeAt Hs' T p := by
  have h5 := h .h5 (Ne.symm hu.2.2.2.2.2.2.1)
  funext s g
  simp only [tapeAt, realPads, sibAnswers, h5]

lemma hyb2'_agreeOff : hyb2' Hs T st r k = hyb2' Hs' T st r k := by
  funext y
  simp only [hyb2', proveIdeal2_agreeOff hu h T st r k, tapeAt_agreeOff hu h T,
    pendAt_agreeOff hu h T (st1 st), fb2_agreeOff hu h T st r]

lemma hyb3'_agreeOff : hyb3' Hs T st r k = hyb3' Hs' T st r k := by
  funext b hid
  simp only [hyb3', proveIdeal2_agreeOff hu h T st r k, fillSib_agreeOff hu h T (st1 st)]

end Congr2

/-- **The simulated two-phase run reads only `μ`, `H₄`, `H₁` and `H₂¹`** (for `chal1`). -/
lemma simRun2_agreeOff {kd : Kind} {Hs Hs' : Hashes} (h : Hs.AgreeOff kd Hs') (h1 : kd ≠ .mu)
    (h2 : kd ≠ .muDelayed) (h3 : kd ≠ .h4) (h4 : kd ≠ .h1) (h5 : kd ≠ .h21) (st : Statement)
    (n : ℕ) (k : Cont2) : simRun2 Hs st n k = simRun2 Hs' st n k := by
  have hP := h.pubOf h1 h2 h3 h4 (st1 st)
  have hc := h.chal1 h5
  funext c
  simp only [simRun2, simPhase1, phase1Of, tC1, hP, hc]

/-- A function of the record that does not read `H₃` or `H₂³` sees `recH` as `rec5`. -/
lemma recH_eq_rec5 {α : Sort*} (F : Hashes → α)
    (hF : ∀ (kd : Kind) (Hs Hs' : Hashes), Unread kd → Hs.AgreeOff kd Hs' → F Hs = F Hs')
    (Hb : Hashes) (st : Statement) (w : ByteArray) (G3 : Tab3) (G2 : Tab2G st.params)
    (G5 : Tab5F) : F (recH Hb st w G3 G2 G5) = F (rec5 Hb G5) := by
  obtain ⟨a1, a2⟩ := recH_rec5 (Hb := Hb) (st := st) (w := w) G3 G2 G5
  exact (hF _ _ _ unread_h23 a1).trans (hF _ _ _ unread_h3 a2)

/-! ## The hypotheses -/

/-- **The deterministic hypotheses of the two-phase theorem**: the witness `r ‖ suffix` satisfies
every instance the continuation may pick (`ZKHypQ`), `r` fits, label rows, `N_MASK ≤ 32`. -/
structure Hyp2 (st : Statement) (r : ByteArray) (k : Cont2) : Prop where
  hk : ∀ o x sfx, k o = some (x, sfx) → ZKHypQ (withInst st x) (r ++ sfx) x.sys
  hr : r.size ≤ st.params.witnessBytes
  hlr : st.params.labelRows = true
  hnm : st.params.nMask ≤ 32

lemma Hyp2.hlab {st : Statement} {r : ByteArray} {k : Cont2} (h : Hyp2 st r k) :
    st.params.labelRowOffset + 128 ≤ st.params.correctionRows := by
  obtain ⟨h1, -, -, h2⟩ := labelRows_sizes h.hlr
  omega

lemma Hyp2.run {st : Statement} {r : ByteArray} {k : Cont2} (h : Hyp2 st r k) {Hs : Hashes}
    (hHs : HashesWF Hs) : RunHyp2 Hs CrtGen.tables st r k :=
  RunHyp2.of_tables h.hk h.hr h.hnm hHs h.hlab

lemma Hyp2.extract {st : Statement} {r : ByteArray} {k : Cont2} (h : Hyp2 st r k) :
    r.extract 0 st.params.witnessBytes = r := by
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le h.hr

/-! ## The real run, in hybrid form -/

section Bridge

variable (Hs : Hashes) (T : CrtTables) (st : Statement) (r : ByteArray) (k : Cont2)

/-- Step 1's output at the root seed and `iv_pre` `x`: the proof buffer and `chal1`. -/
def out1 (x : Bytes 16 × Bytes 16) : ByteArray × ByteArray :=
  ((pendAt Hs T (st1 st) r x).proof, (pendAt Hs T (st1 st) r x).chal1)

/-- **The prefix the grinding answers are read at**: the instance's grinding prefix (`pre2`) if the
continuation continues, else the empty prefix (the run then reads no grinding answer). -/
noncomputable def preP (x : Bytes 16 × Bytes 16) : ByteArray :=
  if (k (out1 Hs T st r x)).isSome then pre2 Hs T st r k x else ByteArray.empty

lemma out1_agreeOff {kd : Kind} {Hs Hs' : Hashes} (hu : Unread kd) (h : Hs.AgreeOff kd Hs') :
    out1 Hs T st r = out1 Hs' T st r := by
  funext x
  simp only [out1, pendAt_agreeOff hu h T (st1 st)]

lemma preP_agreeOff {kd : Kind} {Hs Hs' : Hashes} (hu : Unread kd) (h : Hs.AgreeOff kd Hs') :
    preP Hs T st r k = preP Hs' T st r k := by
  funext x
  simp only [preP, out1_agreeOff T st r hu h, pre2_agreeOff hu h T st r k]

/-- **The real two-phase run in hybrid form** (no probability): `hyb2'` at `H₃`'s answer at the
seed input and the `H₂³` answers at the instance's grinding points. -/
theorem realRun2_hyb2' (hR : RunHyp2 Hs T st r k) (rho : ByteArray) :
    realRun2 Hs T st r k rho = hyb2' Hs T st r k
      ((h3Seed Hs ((st1 st).mu1 Hs) r rho).1, (h3Seed Hs ((st1 st).mu1 Hs) r rho).2,
        realGrind Hs (pre2 Hs T st r k (h3Seed Hs ((st1 st).mu1 Hs) r rho))) := by
  rw [realRun2_eq Hs T st r k rho hR.hk hR.hHs hR.hbavc (hR.hcrt rho) hR.hlab,
    tapeOf2_eq Hs T st r k hR.hHs]
  rfl

/-- The `H₃` input of the empty `rho` of step 1. -/
def seed2 : ByteArray := (r ++ (st1 st).mu1 Hs ++ ByteArray.empty).push 3

/-- **A record for which the run of hybrid H2 at `x` and `g` is a real two-phase run**: `H₃`
answers the seed input of the empty `rho` with `x`, `H₂³` the grinding points of `pre2 x` with
`g`. -/
noncomputable def recAt2 (x : Bytes 16 × Bytes 16) (g : Grind) : Hashes :=
  (Hs.withTable .h23 (grindInput (pre2 Hs T st r k x)) g).withTable .h3
    (fun _ : Unit => seed2 Hs st r) (fun _ => joinSeed x)

variable {Hs T st r k}

lemma recAt2_agree (x : Bytes 16 × Bytes 16) (g : Grind) :
    Hs.AgreeOff .h23 (Hs.withTable .h23 (grindInput (pre2 Hs T st r k x)) g) ∧
    (Hs.withTable .h23 (grindInput (pre2 Hs T st r k x)) g).AgreeOff .h3
      (recAt2 Hs T st r k x g) :=
  ⟨Hs.agreeOff_withTable .h23 _ g, Hashes.agreeOff_withTable _ .h3 _ _⟩

/-- A function of the record that does not read `H₃` or `H₂³` sees `recAt2` as the base record. -/
lemma recAt2_eq {α : Sort*} (F : Hashes → α)
    (hF : ∀ (kd : Kind) (Hs Hs' : Hashes), Unread kd → Hs.AgreeOff kd Hs' → F Hs = F Hs')
    (x : Bytes 16 × Bytes 16) (g : Grind) : F (recAt2 Hs T st r k x g) = F Hs :=
  ((hF _ _ _ unread_h23 (recAt2_agree x g).1).trans
    (hF _ _ _ unread_h3 (recAt2_agree x g).2)).symm

lemma recAt2_wf (hHs : HashesWF Hs) (x : Bytes 16 × Bytes 16) (g : Grind) :
    HashesWF (recAt2 Hs T st r k x g) :=
  (hHs.withTable .h23 _ g).withTable .h3 _ _

lemma recAt2_h3Seed (x : Bytes 16 × Bytes 16) (g : Grind) :
    h3Seed (recAt2 Hs T st r k x g) ((st1 st).mu1 (recAt2 Hs T st r k x g)) r ByteArray.empty =
      x := by
  rw [recAt2_eq (fun H => (st1 st).mu1 H) (fun _ _ _ hu h => h.mu1' hu (st1 st)) x g]
  have e := Hashes.withTable_enc (Hs.withTable .h23 (grindInput (pre2 Hs T st r k x)) g) .h3
    (fun _ : Unit => seed2 Hs st r) (fun _ => joinSeed x) ()
  unfold h3Seed
  rw [show (r ++ (st1 st).mu1 Hs ++ ByteArray.empty).push 3 = seed2 Hs st r from rfl]
  rw [show (recAt2 Hs T st r k x g).hash .h3 (seed2 Hs st r) = ba (joinSeed x) from e]
  exact splitSeed_joinSeed x

lemma recAt2_realGrind (x : Bytes 16 × Bytes 16) (g : Grind) :
    realGrind (recAt2 Hs T st r k x g) (pre2 Hs T st r k x) = g := by
  funext c
  simp only [realGrind]
  rw [show (recAt2 Hs T st r k x g).hash .h23 =
      (Hs.withTable .h23 (grindInput (pre2 Hs T st r k x)) g).hash .h23 from
      ((recAt2_agree x g).2 .h23 (by decide)).symm,
    show (AES.pushLE32 (pre2 Hs T st r k x) c.val.toUInt32).push 11 =
      grindInput (pre2 Hs T st r k x) c from rfl,
    Hashes.withTable_enc Hs .h23 (grindInput _) g c, keyOf_eq (grindInput_injective _)]
  exact blk_ba _

lemma step1_eq_pendAt (hHs : HashesWF Hs) (rho : ByteArray) :
    step1 Hs T st r rho = pendAt Hs T (st1 st) r (h3Seed Hs ((st1 st).mu1 Hs) r rho) :=
  voleGen_eq_pendAt Hs hHs T (st1 st) r rho

variable (Hs st r k) in
/-- **The run of hybrid H2 is a real two-phase run**, for the record `recAt2`. -/
theorem realRun2_recAt2 (hHs : HashesWF Hs) (hh : Hyp2 st r k) (x : Bytes 16 × Bytes 16)
    (g : Grind) :
    realRun2 (recAt2 Hs CrtGen.tables st r k x g) CrtGen.tables st r k ByteArray.empty =
      hyb2' Hs CrtGen.tables st r k (x.1, x.2, g) := by
  rw [realRun2_hyb2' _ _ _ _ _ (hh.run (recAt2_wf hHs x g)), recAt2_h3Seed,
    recAt2_eq (fun H => pre2 H CrtGen.tables st r k) (fun _ _ _ hu h => pre2_agreeOff hu h _ _ _ _),
    recAt2_realGrind]
  exact recAt2_eq (fun H => hyb2' H CrtGen.tables st r k (x.1, x.2, g))
    (fun _ _ _ hu h => by rw [hyb2'_agreeOff hu h]) x g

variable (Hs st r k) in
/-- **Hybrid H2 at `x` and `g`, as a real two-phase run**: step 1's output, then step 2 of the
record `recAt2` if the continuation continues. -/
theorem hyb2'_eq (hHs : HashesWF Hs) (hh : Hyp2 st r k) (x : Bytes 16 × Bytes 16) (g : Grind) :
    hyb2' Hs CrtGen.tables st r k (x.1, x.2, g) =
      ((out1 Hs CrtGen.tables st r x).1, (out1 Hs CrtGen.tables st r x).2,
        (k (out1 Hs CrtGen.tables st r x)).map fun y =>
          Prover.proveCommit (recAt2 Hs CrtGen.tables st r k x g) (withInst st y.1) y.2
            (pendAt Hs CrtGen.tables (st1 st) r x)) := by
  rw [← realRun2_recAt2 Hs st r k hHs hh x g]
  have e : step1 (recAt2 Hs CrtGen.tables st r k x g) CrtGen.tables st r ByteArray.empty =
      pendAt Hs CrtGen.tables (st1 st) r x := by
    rw [step1_eq_pendAt (recAt2_wf hHs x g), recAt2_h3Seed]
    exact recAt2_eq (fun H => pendAt H CrtGen.tables (st1 st) r x)
      (fun _ _ _ hu h => pendAt_agreeOff hu h _ _ _ _) x g
  simp only [realRun2, e, out1]

variable (Hs st r k) in
/-- **If the continuation stops, hybrid H2 does not read the grinding answers.** -/
theorem hyb2'_none (hHs : HashesWF Hs) (hh : Hyp2 st r k) (x : Bytes 16 × Bytes 16) (g : Grind)
    (hk : k (out1 Hs CrtGen.tables st r x) = none) :
    hyb2' Hs CrtGen.tables st r k (x.1, x.2, g) =
      ((out1 Hs CrtGen.tables st r x).1, (out1 Hs CrtGen.tables st r x).2, none) := by
  rw [hyb2'_eq Hs st r k hHs hh x g, hk]
  rfl

variable (Hs st r k) in
lemma step1_recAt2 (hHs : HashesWF Hs) (x : Bytes 16 × Bytes 16) (g : Grind) :
    step1 (recAt2 Hs CrtGen.tables st r k x g) CrtGen.tables st r ByteArray.empty =
      pendAt Hs CrtGen.tables (st1 st) r x := by
  rw [step1_eq_pendAt (recAt2_wf hHs x g), recAt2_h3Seed]
  exact recAt2_eq (fun H => pendAt H CrtGen.tables (st1 st) r x)
    (fun _ _ _ hu h => pendAt_agreeOff hu h _ _ _ _) x g

variable (Hs st r k) in
/-- **Hybrid H2 with an accepted grinding answer and a continuation that continues** returns the
proof of the ideal-tape fields. -/
theorem hyb2'_ok (hHs : HashesWF Hs) (hh : Hyp2 st r k) (x : Bytes 16 × Bytes 16) (g : Grind)
    {ctr : ℕ} {δ : Bytes 16} (hg : firstHit g = some (ctr, δ)) {y : Inst2} {sfx : ByteArray}
    (hk1 : k (out1 Hs CrtGen.tables st r x) = some (y, sfx)) :
    hyb2' Hs CrtGen.tables st r k (x.1, x.2, g) =
      ((out1 Hs CrtGen.tables st r x).1, (out1 Hs CrtGen.tables st r x).2,
        some (.ok (simAssemble st.params
          (tapeAt Hs CrtGen.tables st.params (pendAt Hs CrtGen.tables (st1 st) r x) g).1 ctr δ
          (fieldsOf Hs CrtGen.tables (withInst st y) (r ++ sfx) y.sys
            (tapeAt Hs CrtGen.tables st.params (pendAt Hs CrtGen.tables (st1 st) r x) g).1 ctr δ
            (tapeAt Hs CrtGen.tables st.params (pendAt Hs CrtGen.tables (st1 st) r x) g).2).1))) := by
  have e := hyb2'_eq Hs st r k hHs hh x g
  set t := tapeAt Hs CrtGen.tables st.params (pendAt Hs CrtGen.tables (st1 st) r x) g with ht
  have hg' : t.1.2.1 = g := rfl
  have hu : hyb2' Hs CrtGen.tables st r k (x.1, x.2, g) =
      ((idealPhase1 Hs CrtGen.tables (st1 st) r t.1 ctr δ t.2).1,
        (idealPhase1 Hs CrtGen.tables (st1 st) r t.1 ctr δ t.2).2,
        (k (idealPhase1 Hs CrtGen.tables (st1 st) r t.1 ctr δ t.2)).map fun z =>
          idealCore Hs CrtGen.tables (withInst st z.1) (r ++ z.2) t.1 ctr δ t.2) := by
    show proveIdeal2 Hs CrtGen.tables st r k (t, fb2 Hs CrtGen.tables st r x) = _
    simp only [proveIdeal2, hg', hg]
  have e' := hu.symm.trans e
  have h1 : (idealPhase1 Hs CrtGen.tables (st1 st) r t.1 ctr δ t.2).1 =
      (out1 Hs CrtGen.tables st r x).1 := by have := congrArg Prod.fst e'; exact this
  have h2 : (idealPhase1 Hs CrtGen.tables (st1 st) r t.1 ctr δ t.2).2 =
      (out1 Hs CrtGen.tables st r x).2 := by have := congrArg (fun z => z.2.1) e'; exact this
  have ho : idealPhase1 Hs CrtGen.tables (st1 st) r t.1 ctr δ t.2 = out1 Hs CrtGen.tables st r x :=
    Prod.ext h1 h2
  have hz := hh.hk _ _ _ hk1
  rw [hu, ho, hk1, Option.map_some, idealCore_fields Hs CrtGen.tables (withInst st y) (r ++ sfx)
    y.sys hz.hvals hz.hdeg hz.hd hz.hd' hz.hI hz.hsat]

/-- **The two-phase grinding prefix has `preLen` bytes** (QuickSilver succeeds), for a step 1 at
any witness prefix. -/
theorem realPre_pendAt_size (hHs : HashesWF Hs) (st' : Statement) (w : ByteArray)
    {cs : ByteArray → ByteArray → System GF128} (h : ZKHypQ st' w cs) (wP : ByteArray)
    (x : Bytes 16 × Bytes 16) :
    (realPre Hs st' (pendAt Hs T st' wP x) w).size = preLen st'.params := by
  set s := pendAt Hs T st' wP x
  have h0 : ∀ i, gfOfBytes (Proof.mk st'.params (Prover.assemble st'.params
      (realF1 st'.params s w))).qsProof (16 * i) = 0 := by
    intro i
    rw [(fields_assemble st'.params _).2.2.2.2.1]
    show gfOfBytes (Prover.fit s.fields.qsProof _) _ = 0
    rw [show s.fields.qsProof = ByteArray.empty from rfl, fit_empty, gfOfBytes_zeros]
  have hq := qsProve_eq (Proof.mk st'.params (Prover.assemble st'.params (realF1 st'.params s w)))
    (realC2 Hs st' s w) (st'.values s.chal1 (st'.combBytes Hs (realC2 Hs st' s w))) s.vRows s.vMask
    s.uMask w (cs s.chal1 (st'.combBytes Hs (realC2 Hs st' s w))) (h.hvals _ _) (h.hdeg _ _) h.hd
    h.hd' h0 h.hI (h.hsat _ _)
  rw [realPre, hq]
  simp only [ByteArray.size_append, gfsToBytes_size, Array.size_map, Array.size_range,
    gfToBytes_size', preLen]
  rw [realC2, chal2, hHs]
  rfl

lemma pre2_eq_of {x : Bytes 16 × Bytes 16} {y : Inst2} {sfx : ByteArray}
    (hk1 : k (out1 Hs T st r x) = some (y, sfx)) :
    pre2 Hs T st r k x = realPre Hs (withInst st y) (pendAt Hs T (st1 st) r x) (r ++ sfx) := by
  show realPre Hs (withInst st ((k (out1 Hs T st r x)).getD (default, .empty)).1)
    (pendAt Hs T (st1 st) r x) (r ++ ((k (out1 Hs T st r x)).getD (default, .empty)).2) = _
  rw [hk1]
  rfl

lemma pre2_size (hHs : HashesWF Hs) (hh : Hyp2 st r k) {x : Bytes 16 × Bytes 16} {y : Inst2}
    {sfx : ByteArray} (hk1 : k (out1 Hs T st r x) = some (y, sfx)) :
    (pre2 Hs T st r k x).size = preLen st.params := by
  rw [pre2_eq_of hk1]
  exact realPre_pendAt_size hHs (withInst st y) (r ++ sfx) (hh.hk _ _ _ hk1) r x

variable (Hs st r k) in
/-- **(i) The verifier recomputes the two-phase prover's grinding prefix, in hybrid H2**: unless
the grinding outcome is bad, a run whose continuation continues returns a proof, and `vPre` for
the instance picked recomputes `pre2`. -/
theorem hyb2'_vPre (hHs : HashesWF Hs) (hh : Hyp2 st r k) (x : Bytes 16 × Bytes 16) (g : Grind)
    (hg : ¬ GrindBad CrtGen.tables g) {y : Inst2} {sfx : ByteArray}
    (hk1 : k (out1 Hs CrtGen.tables st r x) = some (y, sfx)) :
    ∃ proof, hyb2' Hs CrtGen.tables st r k (x.1, x.2, g) =
        ((out1 Hs CrtGen.tables st r x).1, (out1 Hs CrtGen.tables st r x).2, some (.ok proof)) ∧
      vPre Hs CrtGen.tables (withInst st y) proof = pre2 Hs CrtGen.tables st r k x := by
  set T := CrtGen.tables
  obtain ⟨hnone, hΔ⟩ := not_or.1 hg
  obtain ⟨⟨ctr, δ⟩, hf⟩ := Option.ne_none_iff_exists'.1 hnone
  have hd : deltaOf g = δ := by unfold deltaOf; rw [hf]; rfl
  have hok := hyb2'_ok Hs st r k hHs hh x g hf hk1
  refine ⟨_, hok, ?_⟩
  set prf := simAssemble st.params (tapeAt Hs T st.params (pendAt Hs T (st1 st) r x) g).1 ctr δ
    (fieldsOf Hs T (withInst st y) (r ++ sfx) y.sys
      (tapeAt Hs T st.params (pendAt Hs T (st1 st) r x) g).1 ctr δ
      (tapeAt Hs T st.params (pendAt Hs T (st1 st) r x) g).2).1 with hprf
  set R' := recAt2 Hs T st r k x g
  have e := hyb2'_eq Hs st r k hHs hh x g
  rw [hok, hk1, Option.map_some] at e
  have hp : Prover.proveCommit R' (withInst st y) sfx (pendAt Hs T (st1 st) r x) = .ok prf :=
    (Option.some.inj (congrArg (fun z => z.2.2) e)).symm
  have hs1 : step1 R' T st r ByteArray.empty = pendAt Hs T (st1 st) r x :=
    step1_recAt2 Hs st r k hHs x g
  have hz := hh.hk _ _ _ hk1
  have hdel : ({ params := st.params, bytes := prf } : Proof).delta = ba δ := by
    rw [hprf, simAssemble, (fields_assemble st.params _).2.2.2.2.2.2.1]
    exact fit_of_size (size_ba _)
  have hΔ' : (W128.rowMul (BAVC.deltaBit
      ({ params := (withInst st y).params, bytes := prf } : Proof).delta) 120 T.wCrt).toGF ≠ 0 := by
    rw [show ({ params := (withInst st y).params, bytes := prf } : Proof) =
      { params := st.params, bytes := prf } from rfl, hdel]
    rw [hd] at hΔ
    exact hΔ
  have hv := vPre_proveCommit R' (recAt2_wf hHs x g) bavcComplete T (withInst st y) _ r
    ByteArray.empty (withInst st y).binder1 sfx prf rfl rfl (by
      show Prover.proveCommit R' (withInst st y) sfx (step1 R' T st r ByteArray.empty) = _
      rw [hs1]; exact hp)
    (crtComplete R' st.params _ r ByteArray.empty _ hh.hlab) hΔ' y.sys hz.hvals hz.hdeg hz.hd hz.hd'
  have hs1' : Prover.voleGen R' T (withInst st y).params ((withInst st y).mu1 R') r ByteArray.empty
      (withInst st y).binder1 = pendAt Hs T (st1 st) r x := hs1
  rw [hs1', recAt2_eq (fun H => vPre H T (withInst st y))
      (fun _ _ _ hu h => vPre_agreeOff hu h _ _) x g,
    recAt2_eq (fun H => realPre H (withInst st y) (pendAt Hs T (st1 st) r x) (r ++ sfx))
      (fun _ _ _ hu h => realPre_agreeOff hu h _ _ _) x g] at hv
  rw [hv, pre2_eq_of hk1]

end Bridge

/-! ## The real run with the tables -/

section Real

variable (Hb : Hashes) (st : Statement) (r : ByteArray) (k : Cont2)

/-- **The real run on the record with the tables, in hybrid form** (no probability): `hyb2'` on
the record without the `H₂³` table, at `H₃`'s answer `G3 ρ` and the `H₂³` table's answers at the
grinding points of `preP` (with the `H₅` table only). -/
theorem real_form (hHb : HashesWF Hb) (hh : Hyp2 st r k) (G3 : Tab3) (G2 : Tab2G st.params)
    (G5 : Tab5F) (ρ : Bytes 16) :
    realRun2 (recH Hb (st1 st) r G3 G2 G5) CrtGen.tables st r k (ba ρ) =
      hyb2' (recB Hb (st1 st) r G3 G5) CrtGen.tables st r k
        ((splitSeed (G3 ρ)).1, (splitSeed (G3 ρ)).2,
          G2 ∘ key2 st.params (preP (rec5 Hb G5) CrtGen.tables st r k (splitSeed (G3 ρ)))) := by
  have hRwf : HashesWF (recH Hb (st1 st) r G3 G2 G5) :=
    recH_wf (st := st1 st) (w := r) hHb G3 G2 G5
  have hBwf : HashesWF (recB Hb (st1 st) r G3 G5) :=
    recH_wf (st := st1 st) (w := r) hHb G3 _ G5
  have hs : h3Seed (recH Hb (st1 st) r G3 G2 G5) ((st1 st).mu1 (recH Hb (st1 st) r G3 G2 G5)) r
      (ba ρ) = splitSeed (G3 ρ) := by
    have e1 := recH_h3Seed (Hb := Hb) (st := st1 st) (w := r) G3 G2 G5 ρ
    have e2 : r.extract 0 (st1 st).params.witnessBytes = r := hh.extract
    rw [e2] at e1
    exact e1
  rw [realRun2_hyb2' _ CrtGen.tables st r k (hh.run hRwf), hs]
  have hB : hyb2' (recH Hb (st1 st) r G3 G2 G5) CrtGen.tables st r k =
      hyb2' (recB Hb (st1 st) r G3 G5) CrtGen.tables st r k :=
    hyb2'_agreeOff unread_h23 (recH_agreeOff_h23 (st := st1 st) (w := r) G3 G2 (fun _ => 0) G5)
      CrtGen.tables st r k
  have hpre : pre2 (recH Hb (st1 st) r G3 G2 G5) CrtGen.tables st r k =
      pre2 (rec5 Hb G5) CrtGen.tables st r k :=
    recH_eq_rec5 (fun H => pre2 H CrtGen.tables st r k)
      (fun _ _ _ hu h => pre2_agreeOff hu h _ _ _ _) Hb (st1 st) r G3 G2 G5
  have hout : ∀ G2', out1 (recH Hb (st1 st) r G3 G2' G5) CrtGen.tables st r =
      out1 (rec5 Hb G5) CrtGen.tables st r :=
    fun G2' => recH_eq_rec5 (fun H => out1 H CrtGen.tables st r)
      (fun _ _ _ hu h => out1_agreeOff CrtGen.tables st r hu h) Hb (st1 st) r G3 G2' G5
  rw [hB]
  by_cases hc : (k (out1 (rec5 Hb G5) CrtGen.tables st r (splitSeed (G3 ρ)))).isSome
  · obtain ⟨⟨y, sfx⟩, hk1⟩ := Option.isSome_iff_exists.1 hc
    have hsz : (pre2 (recH Hb (st1 st) r G3 G2 G5) CrtGen.tables st r k (splitSeed (G3 ρ))).size =
        preLen st.params :=
      pre2_size hRwf hh (by rw [hout]; exact hk1)
    have hg : realGrind (recH Hb (st1 st) r G3 G2 G5)
        (pre2 (recH Hb (st1 st) r G3 G2 G5) CrtGen.tables st r k (splitSeed (G3 ρ))) =
        G2 ∘ key2 st.params
          (pre2 (recH Hb (st1 st) r G3 G2 G5) CrtGen.tables st r k (splitSeed (G3 ρ))) :=
      recH_realGrind (st := st1 st) (w := r) G3 G2 G5 hsz
    rw [hg, hpre]
    simp only [preP, hc, ↓reduceIte]
  · have hk1 : k (out1 (rec5 Hb G5) CrtGen.tables st r (splitSeed (G3 ρ))) = none :=
      Option.not_isSome_iff_eq_none.1 hc
    have hBe : recB Hb (st1 st) r G3 G5 = recH Hb (st1 st) r G3 (fun _ => 0) G5 := rfl
    have hk1' : k (out1 (recB Hb (st1 st) r G3 G5) CrtGen.tables st r (splitSeed (G3 ρ))) =
        none := by rw [hBe, hout]; exact hk1
    rw [hyb2'_none _ st r k hBwf hh _ _ hk1', hyb2'_none _ st r k hBwf hh _ _ hk1']

end Real

/-! ## The simulator's programming -/

section Prog

variable (Hb : Hashes) (T : CrtTables) (st : Statement) (k : Cont2)

/-- **The grinding prefix the simulator recomputes from a two-phase output**: `vPre` (with the
`H₅` table) on the final proof, for the instance the continuation picks from the output's step 1;
the empty prefix if there is no final proof or the continuation stops. -/
noncomputable def outPre2 (G5 : Tab5F) (o : Out2) : ByteArray :=
  match o.2.2, k (o.1, o.2.1) with
  | some (.ok b), some y => vPre (rec5 Hb G5) T (withInst st y.1) b
  | _, _ => ByteArray.empty

/-- **The simulator's `H₂³` table**: `G2` programmed at the grinding points of the recomputed
prefix (`outPre2`), counter `c` answered by `g c`. -/
noncomputable def simTab2 (G5 : Tab5F) (o : Out2) (g : Grind) (G2 : Tab2G st.params) :
    Tab2G st.params :=
  programAt (key2 st.params (outPre2 Hb T st k G5 o)) g G2

/-- The distinguisher, with the `H₂³` table programmed by `simTab2` at the grinding answers `g`. -/
def Dp2 (D : Out2 → Tab3 → Tab2G st.params → Tab5F → Prop) (o : Out2) (g : Grind)
    (v : Vis2 st.params) : Prop :=
  D o v.1 (simTab2 Hb T st k v.2.2 o g v.2.1) v.2.2

end Prog

/-! ## The hybrids before H4 -/

section Pre

variable (Hb : Hashes) (st : Statement) (r : ByteArray) (kf : Tab5F → Cont2)

/-- **H1 with the tables** (two phases): `rho` and the `H₃` table against a uniform seed and
`iv_pre`, for a distinguisher that reads the `H₃` table at `q₃` keys. -/
theorem zk2_h1 (hHb : HashesWF Hb) (hh : ∀ G5, Hyp2 st r (kf G5))
    (D : Out2 → Tab3 → Tab2G st.params → Tab5F → Prop)
    (Q3 : Out2 → Tab3 → Tab2G st.params → Tab5F → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G2 G5, (∀ k ∈ Q3 o G3 G2 G5, G3 k = G3' k) →
      (D o G3 G2 G5 ↔ D o G3' G2 G5))
    {q3 : ℕ} (hq3 : ∀ o G3 G2 G5, (Q3 o G3 G2 G5).card ≤ q3) :
    |pr ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) (fun c =>
        D (realRun2 (recH Hb (st1 st) r c.2.1 c.1.2 c.2.2) CrtGen.tables st r (kf c.2.2) (ba c.1.1))
          c.2.1 c.1.2 c.2.2) -
      pr (((Bytes 16 × Bytes 16) × Tab2G st.params) × (Tab3 × Tab5F)) (fun c =>
        D (hyb2' (recB Hb (st1 st) r c.2.1 c.2.2) CrtGen.tables st r (kf c.2.2)
          (c.1.1.1, c.1.1.2, c.1.2 ∘ key2 st.params (preP (rec5 Hb c.2.2) CrtGen.tables st r (kf c.2.2) c.1.1)))
          c.2.1 c.1.2 c.2.2)| ≤ q3 / 2 ^ 128 := by
  let E0 : (Tab2G st.params × Tab5F) × (Bytes 16 × Tab3) ≃
      (Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F) :=
    { toFun := fun c => ((c.2.1, c.1.1), (c.2.2, c.1.2))
      invFun := fun c => ((c.1.2, c.2.2), (c.1.1, c.2.1))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let E1 : (Tab2G st.params × Tab5F) × (Tab3 × (Bytes 16 × Bytes 16)) ≃
      ((Bytes 16 × Bytes 16) × Tab2G st.params) × (Tab3 × Tab5F) :=
    { toFun := fun c => ((c.2.2, c.1.1), (c.2.1, c.1.2))
      invFun := fun c => ((c.1.2, c.2.2), (c.2.1, c.1.1))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv E0, ← pr_equiv E1]
  refine abs_pr_prod_sub_le _ _ fun a => ?_
  obtain ⟨G2, G5⟩ := a
  let R : Bytes 16 × Bytes 16 → Out2 := fun x =>
    hyb2' (recB Hb (st1 st) r (fun _ => 0) G5) CrtGen.tables st r (kf G5)
      (x.1, x.2, G2 ∘ key2 st.params (preP (rec5 Hb G5) CrtGen.tables st r (kf G5) x))
  have hR : ∀ G3 : Tab3, hyb2' (recB Hb (st1 st) r G3 G5) CrtGen.tables st r (kf G5) =
      hyb2' (recB Hb (st1 st) r (fun _ => 0) G5) CrtGen.tables st r (kf G5) := fun G3 =>
    hyb2'_agreeOff unread_h3 (recH_agreeOff_h3 (st := st1 st) (w := r) G3 (fun _ => 0)
      (fun _ => 0) G5) CrtGen.tables st r (kf G5)
  let A : Bytes 16 × Bytes 16 → Tab3 → Prop := fun v G3 => D (R v) G3 G2 G5
  have h := h3_rom_query ((st1 st).mu1 Hb) r Hb A (fun v G3 => Q3 (R v) G3 G2 G5)
    (fun v G3 G3' hk => hQ3 (R v) G3 G3' G2 G5 hk) (fun v G3 => hq3 _ G3 G2 G5)
  have e1 : pr (Bytes 16 × Tab3) (fun b =>
      D (realRun2 (recH Hb (st1 st) r b.2 G2 G5) CrtGen.tables st r (kf G5) (ba b.1)) b.2 G2 G5) =
      pr (Bytes 16 × (Bytes 16 → Bytes 32)) (fun p =>
        A (h3Seed (Hb.withTable .h3 (seedInput ((st1 st).mu1 Hb) r) p.2) ((st1 st).mu1 Hb) r
          (ba p.1)) p.2) := by
    refine pr_congr fun b => ?_
    simp only [A, R, real_form Hb st r (kf G5) hHb (hh G5), h3Seed_withTable, hR]
  have e2 : pr (Bytes 16 × ((Bytes 16 → Bytes 32) × Bytes 32)) (fun p =>
      A (splitSeed p.2.2) p.2.1) =
      pr (Tab3 × (Bytes 16 × Bytes 16)) (fun b => D (hyb2' (recB Hb (st1 st) r b.1 G5)
        CrtGen.tables st r (kf G5) (b.2.1, b.2.2,
          G2 ∘ key2 st.params (preP (rec5 Hb G5) CrtGen.tables st r (kf G5) b.2))) b.1 G2 G5) := by
    rw [pr_prod_snd (α := Bytes 16)
      (fun q : (Bytes 16 → Bytes 32) × Bytes 32 => A (splitSeed q.2) q.1),
      ← pr_equiv (Equiv.prodCongr (Equiv.refl Tab3) splitEquiv)]
    refine pr_congr fun b => ?_
    simp only [A, R, hR]
    rfl
  have e1' : pr (Bytes 16 × Tab3) (fun b =>
      D (realRun2 (recH Hb (st1 st) r b.2 G2 G5) CrtGen.tables st r (kf G5) (ba b.1)) b.2 G2 G5) =
      pr (Bytes 16 × Tab3) (fun b =>
        D (realRun2 (recH Hb (st1 st) r (E0 ((G2, G5), b)).2.1 (E0 ((G2, G5), b)).1.2
          (E0 ((G2, G5), b)).2.2) CrtGen.tables st r (kf (E0 ((G2, G5), b)).2.2) (ba (E0 ((G2, G5), b)).1.1))
          (E0 ((G2, G5), b)).2.1 (E0 ((G2, G5), b)).1.2 (E0 ((G2, G5), b)).2.2) := rfl
  have e2' : pr (Tab3 × (Bytes 16 × Bytes 16)) (fun b => D (hyb2' (recB Hb (st1 st) r b.1 G5)
        CrtGen.tables st r (kf G5) (b.2.1, b.2.2,
          G2 ∘ key2 st.params (preP (rec5 Hb G5) CrtGen.tables st r (kf G5) b.2))) b.1 G2 G5) =
      pr (Tab3 × (Bytes 16 × Bytes 16)) (fun b =>
        D (hyb2' (recB Hb (st1 st) r (E1 ((G2, G5), b)).2.1 (E1 ((G2, G5), b)).2.2)
          CrtGen.tables st r (kf (E1 ((G2, G5), b)).2.2) ((E1 ((G2, G5), b)).1.1.1, (E1 ((G2, G5), b)).1.1.2,
            (E1 ((G2, G5), b)).1.2 ∘ key2 st.params (preP (rec5 Hb (E1 ((G2, G5), b)).2.2)
              CrtGen.tables st r (kf (E1 ((G2, G5), b)).2.2) (E1 ((G2, G5), b)).1.1)))
          (E1 ((G2, G5), b)).2.1 (E1 ((G2, G5), b)).1.2 (E1 ((G2, G5), b)).2.2) := rfl
  rw [← e1', ← e2', e1, ← e2]
  exact h

/-- **Grinding with `H₂³` visible: programming is perfect** (exact, two phases). -/
theorem zk2_prog (D : Out2 → Tab3 → Tab2G st.params → Tab5F → Prop) :
    |pr (((Bytes 16 × Bytes 16) × Tab2G st.params) × (Tab3 × Tab5F)) (fun c =>
        D (hyb2' (recB Hb (st1 st) r c.2.1 c.2.2) CrtGen.tables st r (kf c.2.2)
          (c.1.1.1, c.1.1.2, c.1.2 ∘ key2 st.params (preP (rec5 Hb c.2.2) CrtGen.tables st r (kf c.2.2) c.1.1)))
          c.2.1 c.1.2 c.2.2) -
      pr (((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5F)) (fun c =>
        D (hyb2' (recB Hb (st1 st) r c.2.1 c.2.2) CrtGen.tables st r (kf c.2.2) (c.1.1.1, c.1.1.2, c.1.2.2))
          c.2.1 (programAt (key2 st.params (preP (rec5 Hb c.2.2) CrtGen.tables st r (kf c.2.2) c.1.1))
            c.1.2.2 c.1.2.1) c.2.2)| ≤ 0 := by
  refine abs_pr_prod_sub_le' _ _ fun v => ?_
  obtain ⟨G3, G5⟩ := v
  rw [abs_nonpos_iff, sub_eq_zero]
  exact pr_program_eq (C := Bytes 16 × Bytes 16) (R := Bytes 16)
    (x := fun c => key2 st.params (preP (rec5 Hb G5) CrtGen.tables st r (kf G5) c))
    (fun c => key2_injective _ _)
    (fun c (u : Grind) (G2 : Tab2G st.params) =>
      D (hyb2' (recB Hb (st1 st) r G3 G5) CrtGen.tables st r (kf G5) (c.1, c.2, u)) G3 G2 G5)

/-- The hybrid after H4's form: the hidden part from the root seed is the real run's, with any
fallback block. -/
lemma hyb3'_hiddenOut (k : Cont2) (Hs : Hashes) (hHs : HashesWF Hs)
    (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows) (x : Bytes 16 × Bytes 16)
    (g : Grind) (fb : Fallback st.params) :
    hyb3' Hs CrtGen.tables st r k ((x.2, g), fb)
        (hiddenOut st.params (ivOfPre Hs (st1 st) x.2) (ba (deltaOf g)) x.1) =
      proveIdeal2 Hs CrtGen.tables st r k
        (tapeAt Hs CrtGen.tables st.params (pendAt Hs CrtGen.tables (st1 st) r x) g, fb) := by
  rw [← real_fillSib2 Hs CrtGen.tables st r k hHs bavcComplete hlab,
    fillSib_tapeAt Hs CrtGen.tables (st1 st) r x.1 x.2 g, pendAt_iv]
  rfl

/-- **The programmed points, recomputed from the output, and a uniform fallback block**
(`≤ Pr[GrindBad]`, two phases): outside `GrindBad` an answer is accepted (the fallback block is
not read) and the recomputed prefix is `preP` (`hyb2'_vPre`; the empty prefix when the
continuation stops, `hyb2'_none`). -/
theorem zk2_keys (hHb : HashesWF Hb) (hh : ∀ G5, Hyp2 st r (kf G5))
    (D : Out2 → Tab3 → Tab2G st.params → Tab5F → Prop) :
    |pr (((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5F)) (fun c =>
        D (hyb2' (recB Hb (st1 st) r c.2.1 c.2.2) CrtGen.tables st r (kf c.2.2) (c.1.1.1, c.1.1.2, c.1.2.2))
          c.2.1 (programAt (key2 st.params (preP (rec5 Hb c.2.2) CrtGen.tables st r (kf c.2.2) c.1.1))
            c.1.2.2 c.1.2.1) c.2.2) -
      pr ((((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × Fallback st.params) ×
          (Tab3 × Tab5F)) (fun c =>
        Dp2 Hb CrtGen.tables st (kf c.2.2) D (hyb3' (recB Hb (st1 st) r c.2.1 c.2.2) CrtGen.tables st r (kf c.2.2)
          ((c.1.1.1.2, c.1.1.2.2), c.1.2)
          (hiddenOut st.params (ivOfPre Hb (st1 st) c.1.1.1.2) (ba (deltaOf c.1.1.2.2)) c.1.1.1.1))
          c.1.1.2.2 (c.2.1, c.1.1.2.1, c.2.2))| ≤
      pr Grind (GrindBad CrtGen.tables) := by
  let L : ((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5F) → Prop := fun c =>
    D (hyb2' (recB Hb (st1 st) r c.2.1 c.2.2) CrtGen.tables st r (kf c.2.2) (c.1.1.1, c.1.1.2, c.1.2.2))
      c.2.1 (programAt (key2 st.params (preP (rec5 Hb c.2.2) CrtGen.tables st r (kf c.2.2) c.1.1))
        c.1.2.2 c.1.2.1) c.2.2
  let EF : (((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5F)) ×
      Fallback st.params ≃ (((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) ×
        Fallback st.params) × (Tab3 × Tab5F) :=
    { toFun := fun c => ((c.1.1, c.2), c.1.2)
      invFun := fun c => ((c.1.1, c.2), c.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have e0 : pr (((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5F)) L =
      pr ((((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × Fallback st.params) ×
        (Tab3 × Tab5F)) (fun c => L (c.1.1, c.2)) := by
    rw [← pr_equiv EF, ← pr_prod_fst (β := Fallback st.params) L]
    rfl
  rw [show (fun c : ((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5F) =>
      D (hyb2' (recB Hb (st1 st) r c.2.1 c.2.2) CrtGen.tables st r (kf c.2.2) (c.1.1.1, c.1.1.2, c.1.2.2))
        c.2.1 (programAt (key2 st.params (preP (rec5 Hb c.2.2) CrtGen.tables st r (kf c.2.2) c.1.1))
          c.1.2.2 c.1.2.1) c.2.2) = L from rfl, e0]
  refine (abs_pr_sub_le_of_agree _ _ (fun c => GrindBad CrtGen.tables c.1.1.2.2)
    fun c hc => ?_).trans (le_of_eq ?_)
  · obtain ⟨⟨⟨x, G2, g⟩, fb⟩, G3, G5⟩ := c
    dsimp only at hc ⊢
    have hBwf : HashesWF (recB Hb (st1 st) r G3 G5) := recH_wf (st := st1 st) (w := r) hHb G3 _ G5
    have hiv : ivOfPre (recB Hb (st1 st) r G3 G5) (st1 st) = ivOfPre Hb (st1 st) :=
      recH_ivOfPre (st := st1 st) (w := r) G3 (fun _ => 0) G5
    obtain ⟨⟨ctr, δ⟩, hf⟩ := Option.ne_none_iff_exists'.1 (not_or.1 hc).1
    -- The hybrid after H4's form is hybrid H2 (the fallback block is not read).
    have e1 : hyb3' (recB Hb (st1 st) r G3 G5) CrtGen.tables st r (kf G5) ((x.2, g), fb)
        (hiddenOut st.params (ivOfPre Hb (st1 st) x.2) (ba (deltaOf g)) x.1) =
        hyb2' (recB Hb (st1 st) r G3 G5) CrtGen.tables st r (kf G5) (x.1, x.2, g) := by
      rw [← hiv, hyb3'_hiddenOut st r (kf G5) _ hBwf (hh G5).hlab x g fb]
      exact proveIdeal2_fb _ _ st r (kf G5) (t := tapeAt (recB Hb (st1 st) r G3 G5) CrtGen.tables
        st.params (pendAt (recB Hb (st1 st) r G3 G5) CrtGen.tables (st1 st) r x) g) hf _ _
    have hout : out1 (recB Hb (st1 st) r G3 G5) CrtGen.tables st r = out1 (rec5 Hb G5) CrtGen.tables st r :=
      recH_eq_rec5 (fun H => out1 H CrtGen.tables st r)
        (fun _ _ _ hu h => out1_agreeOff CrtGen.tables st r hu h) Hb (st1 st) r G3 _ G5
    -- The recomputed prefix is `preP`.
    have e2 : outPre2 Hb CrtGen.tables st (kf G5) G5
        (hyb2' (recB Hb (st1 st) r G3 G5) CrtGen.tables st r (kf G5) (x.1, x.2, g)) =
        preP (rec5 Hb G5) CrtGen.tables st r (kf G5) x := by
      rcases hk1 : kf G5 (out1 (rec5 Hb G5) CrtGen.tables st r x) with _ | ⟨y, sfx⟩
      · rw [hyb2'_none _ st r (kf G5) hBwf (hh G5) x g (by rw [hout]; exact hk1)]
        simp only [outPre2, preP, hk1, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      · obtain ⟨proof, hok, hv⟩ := hyb2'_vPre _ st r (kf G5) hBwf (hh G5) x g hc (y := y) (sfx := sfx)
          (by rw [hout]; exact hk1)
        rw [hok]
        have hv' : vPre (rec5 Hb G5) CrtGen.tables (withInst st y) proof =
            pre2 (rec5 Hb G5) CrtGen.tables st r (kf G5) x := by
          rw [← recH_eq_rec5 (fun H => vPre H CrtGen.tables (withInst st y))
              (fun _ _ _ hu h => vPre_agreeOff hu h _ _) Hb (st1 st) r G3 (fun _ => 0) G5,
            ← recH_eq_rec5 (fun H => pre2 H CrtGen.tables st r (kf G5))
              (fun _ _ _ hu h => pre2_agreeOff hu h _ _ _ _) Hb (st1 st) r G3 (fun _ => 0) G5]
          exact hv
        simp only [outPre2, hout, hk1, preP, Option.isSome_some, ↓reduceIte]
        exact hv'
    simp only [L, Dp2, simTab2, e1, e2]
  · rw [pr_prod_fst (β := Tab3 × Tab5F)
      (fun a : ((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × Fallback st.params =>
        GrindBad CrtGen.tables a.1.2.2),
      pr_prod_fst (β := Fallback st.params)
        (fun a : (Bytes 16 × Bytes 16) × (Tab2G st.params × Grind) => GrindBad CrtGen.tables a.2.2),
      pr_prod_snd (α := Bytes 16 × Bytes 16)
        (fun a : Tab2G st.params × Grind => GrindBad CrtGen.tables a.2),
      pr_prod_snd (α := Tab2G st.params) (GrindBad CrtGen.tables)]

end Pre

/-! ## The two-phase ideal run reads `H₅` only at the active gate inputs -/

section Reads2

variable {Hs Hs' : Hashes} (T : CrtTables) (st : Statement) (r : ByteArray) (k : Cont2)

lemma idealCore_h5_congr (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    (hoff : Hs.AgreeOff .h5 Hs') (w : ByteArray) (s : Shared) (ctr : ℕ) (delta : Bytes 16)
    (t : Pads st.params)
    (h : ∀ y ∈ Prover.gateInputsOff st.params T (pubOf Hs st s delta).iv
      (qcolsOf st (pubOf Hs st s delta) delta (correctionsOf st.params (usOf st.params t)))
      W128.zero, Hs.hash .h5 y = Hs'.hash .h5 y) :
    idealCore Hs T st w s ctr delta t = idealCore Hs' T st w s ctr delta t := by
  have hP := hoff.pubOf (by decide) (by decide) (by decide) (by decide) st
  unfold idealCore
  dsimp only
  rw [← hP]
  have hlen := gateInputsOff_length st.params T (pubOf Hs st s delta).iv
    (qcolsOf st (pubOf Hs st s delta) delta (correctionsOf st.params (usOf st.params t))) W128.zero
  rw [cmultIdeal_congr T st hlab _ _ _ _ _ _ (qcolsOf_size st _ _ _) fun e he =>
    h _ (getD_mem_of_lt (by omega))]
  refine idealTail_congr T st w hoff _ _ _ _ _ _ _ _ (tCrt_congr T st hoff _ _ _ _ fun y hy => ?_)
  rw [gateInputs_eq_off] at hy
  exact h y hy

lemma idealPhase1_h5_congr (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    (hoff : Hs.AgreeOff .h5 Hs') (s : Shared) (ctr : ℕ) (delta : Bytes 16) (t : Pads st.params)
    (h : ∀ y ∈ Prover.gateInputsOff st.params T (pubOf Hs st s delta).iv
      (qcolsOf st (pubOf Hs st s delta) delta (correctionsOf st.params (usOf st.params t)))
      W128.zero, Hs.hash .h5 y = Hs'.hash .h5 y) :
    idealPhase1 Hs T st r s ctr delta t = idealPhase1 Hs' T st r s ctr delta t := by
  have hP := hoff.pubOf (by decide) (by decide) (by decide) (by decide) st
  have hc1 := hoff.chal1 (by decide)
  unfold idealPhase1
  dsimp only
  rw [← hP]
  have hlen := gateInputsOff_length st.params T (pubOf Hs st s delta).iv
    (qcolsOf st (pubOf Hs st s delta) delta (correctionsOf st.params (usOf st.params t))) W128.zero
  rw [cmultIdeal_congr T st hlab _ _ _ _ _ _ (qcolsOf_size st _ _ _) fun e he =>
    h _ (getD_mem_of_lt (by omega))]
  simp only [tUt, tC1, tF1, tF0, hP, hc1]

/-- **The two-phase ideal run reads `H₅` only at the active gate inputs of its tape.** -/
theorem proveIdeal2_h5_congr (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    (hoff : Hs.AgreeOff .h5 Hs') (x : IdealTape2 st.params)
    (h : ∀ y ∈ actInputs Hs T (st1 st) x.1.1 x.1.2, Hs.hash .h5 y = Hs'.hash .h5 y) :
    proveIdeal2 Hs T st r k x = proveIdeal2 Hs' T st r k x := by
  obtain ⟨⟨s, t⟩, fb⟩ := x
  unfold proveIdeal2
  rcases hg : firstHit s.2.1 with _ | ⟨ctr, delta⟩
  · rfl
  have hdel : deltaOf s.2.1 = delta := by simp only [deltaOf, hg, Option.map_some, Option.getD_some]
  simp only [actInputs, qcolsTape, hdel] at h
  dsimp only
  rw [idealPhase1_h5_congr T (st1 st) r hlab hoff s ctr delta t h]
  refine congrArg _ (congrArg _ (map_congr_of fun z _ => ?_))
  exact idealCore_h5_congr T (withInst st z.1) hlab hoff (r ++ z.2) s ctr delta t h

end Reads2

/-! ## The hybrids after H4 -/

section Post

variable (Hb : Hashes) (st : Statement) (r : ByteArray)

/-- **The deterministic steps with the tables** (exact, two phases): the unused seed slots, then
the tape. -/
theorem zk2_tape (kf : Tab5F → Cont2) (D : Out2 → Tab3 → Tab2G st.params → Tab5F → Prop) :
    |pr ((Hidden st.params × ((Bytes 16 × Grind) × Fallback st.params)) × Vis2 st.params)
        (fun c => Dp2 Hb CrtGen.tables st (kf c.2.2.2) D (hyb3' (recB Hb (st1 st) r c.2.1 c.2.2.2)
          CrtGen.tables st r (kf c.2.2.2) c.1.2 (hiddenIdeal (ba (deltaOf c.1.2.1.2)) c.1.1)) c.1.2.1.2 c.2) -
      pr (IdealTape2 st.params × Vis2 st.params) (fun c =>
        Dp2 Hb CrtGen.tables st (kf c.2.2.2) D (proveIdeal2 (recB Hb (st1 st) r c.2.1 c.2.2.2) CrtGen.tables
          st r (kf c.2.2.2) (fillSib (recB Hb (st1 st) r c.2.1 c.2.2.2) CrtGen.tables (st1 st) c.1.1, c.1.2))
          c.1.1.1.2.1 c.2)| ≤ 0 := by
  refine abs_pr_prod_sub_le' _ _ fun v => ?_
  rw [abs_nonpos_iff, sub_eq_zero]
  let R := recB Hb (st1 st) r v.1 v.2.2
  let F : Out2 → Grind → Prop := fun o g => Dp2 Hb CrtGen.tables st (kf v.2.2) D o g v
  have e1 : pr (Hidden st.params × ((Bytes 16 × Grind) × Fallback st.params)) (fun y =>
      F (hyb3' R CrtGen.tables st r (kf v.2.2) y.2 (hiddenIdeal (ba (deltaOf y.2.1.2)) y.1)) y.2.1.2) =
      pr (Hidden st.params × ((Bytes 16 × Grind) × Fallback st.params))
        (fun y => F (hyb3' R CrtGen.tables st r (kf v.2.2) y.2 y.1) y.2.1.2) :=
    pr_congr fun y => by rw [hyb3'_zeroTail]
  have e2 : pr (IdealTape2 st.params) (fun t =>
      F (proveIdeal2 R CrtGen.tables st r (kf v.2.2) (fillSib R CrtGen.tables (st1 st) t.1, t.2)) t.1.1.2.1) =
      pr (Hidden st.params × ((Bytes 16 × Grind) × Fallback st.params))
        (fun y => F (hyb3' R CrtGen.tables st r (kf v.2.2) y.2 y.1) y.2.1.2) := by
    rw [← pr_equiv (tapeEquiv2 st.params), ← pr_prod_fst (β := Sib)
      (fun y : Hidden st.params × ((Bytes 16 × Grind) × Fallback st.params) =>
        F (hyb3' R CrtGen.tables st r (kf v.2.2) y.2 y.1) y.2.1.2)]
    refine pr_congr fun x => ?_
    rw [show (tapeEquiv2 st.params x).1 = tapeOfHidden x.1.2.1.1 x.1.2.1.2 x.1.1 x.2 from rfl,
      show (tapeEquiv2 st.params x).2 = x.1.2.2 from rfl, hyb3',
      fillSib_tapeOfHidden R CrtGen.tables (st1 st) _ _ _ x.2 fun _ => fun _ => 0]
    rfl
  exact e1.trans e2.symm

/-- **The ideal two-phase run on a uniform tape is the simulated run**, with the shared tape
(which carries the grinding answers) visible (exact). -/
theorem proveIdeal2_close_shared (k : Cont2) (Hs : Hashes) (hh : Hyp2 st r k) :
    Close 0 (fun t : IdealTape2 st.params =>
        (proveIdeal2 Hs CrtGen.tables st r k t, t.1.1.2.1))
      (fun c : SimCoins2 st.params => (simRun2 Hs st r.size k c, c.1.1.2.1)) := by
  have hs : ∀ (fb : Fallback st.params) (s : Shared), Close 0
      (fun t : Pads st.params => (proveIdeal2 Hs CrtGen.tables st r k ((s, t), fb), s.2.1))
      (fun f : SimFields st.params => (simRun2 Hs st r.size k ((s, f), fb), s.2.1)) :=
    fun fb s => (proveIdeal2_close_at Hs CrtGen.tables st r k hh.hk hh.hr hh.hnm
      maskInvOk_tables fb s).map fun o => (o, s.2.1)
  have h1 : ∀ fb, Close 0
      (fun t : IdealTape st.params => (proveIdeal2 Hs CrtGen.tables st r k (t, fb), t.1.2.1))
      (fun c : SimCoins st.params => (simRun2 Hs st r.size k (c, fb), c.1.2.1)) := fun fb => by
    convert Close.prod_right
      (X := fun s (t : Pads st.params) => (proveIdeal2 Hs CrtGen.tables st r k ((s, t), fb), s.2.1))
      (Y := fun s (f : SimFields st.params) => (simRun2 Hs st r.size k ((s, f), fb), s.2.1)) (hs fb)
  convert Close.prod_left
    (X := fun (t : IdealTape st.params) fb => (proveIdeal2 Hs CrtGen.tables st r k (t, fb), t.1.2.1))
    (Y := fun (c : SimCoins st.params) fb => (simRun2 Hs st r.size k (c, fb), c.1.2.1)) h1

/-- **The ideal two-phase run on a uniform tape is the simulator**, with the tables and the
grinding answers (exact); the simulated run does not read the tables (`simRun2_agreeOff`). -/
theorem zk2_sim (kf : Tab5F → Cont2) (hh : ∀ G5, Hyp2 st r (kf G5)) (D : Out2 → Tab3 → Tab2G st.params → Tab5F → Prop) :
    |pr (IdealTape2 st.params × Vis2 st.params) (fun c =>
        Dp2 Hb CrtGen.tables st (kf c.2.2.2) D (proveIdeal2 (recB Hb (st1 st) r c.2.1 c.2.2.2) CrtGen.tables
          st r (kf c.2.2.2) c.1) c.1.1.1.2.1 c.2) -
      pr (SimCoins2 st.params × Vis2 st.params) (fun c =>
        Dp2 Hb CrtGen.tables st (kf c.2.2.2) D (simRun2 Hb st r.size (kf c.2.2.2) c.1) c.1.1.1.2.1 c.2)| ≤ 0 :=
  abs_pr_prod_sub_le' _ _ fun v => by
    have hB : simRun2 (recB Hb (st1 st) r v.1 v.2.2) st r.size (kf v.2.2) = simRun2 Hb st r.size (kf v.2.2) := by
      have a1 := Hb.agreeOff_withTable .h3
        (seedInput ((st1 st).mu1 Hb) (r.extract 0 (st1 st).params.witnessBytes)) v.1
      have a2 := (Hb.withTable .h3 (seedInput ((st1 st).mu1 Hb)
        (r.extract 0 (st1 st).params.witnessBytes)) v.1).agreeOff_withTable .h23
          (enc2 (st1 st).params) (fun _ => 0)
      have a3 := ((Hb.withTable .h3 (seedInput ((st1 st).mu1 Hb)
        (r.extract 0 (st1 st).params.witnessBytes)) v.1).withTable .h23
          (enc2 (st1 st).params) (fun _ => 0)).agreeOff_withTable .h5 enc5 v.2.2
      exact ((simRun2_agreeOff a1 (by decide) (by decide) (by decide) (by decide) (by decide) st
        r.size (kf v.2.2)).trans ((simRun2_agreeOff a2 (by decide) (by decide) (by decide) (by decide)
          (by decide) st r.size (kf v.2.2)).trans (simRun2_agreeOff a3 (by decide) (by decide) (by decide)
            (by decide) (by decide) st r.size (kf v.2.2)))).symm
    have := proveIdeal2_close_shared st r (kf v.2.2) (recB Hb (st1 st) r v.1 v.2.2) (hh v.2.2)
      (fun os => Dp2 Hb CrtGen.tables st (kf v.2.2) D os.1 os.2 v)
    dsimp only at this ⊢
    rw [← hB]
    exact this

end Post

/-! ## H6 with the tables, two phases -/

section H6

attribute [local instance] decEqW128

variable (Hs : Hashes) (st : Statement) (r : ByteArray) (k : Cont2)

/-- With `H₅` a table, the two-phase ideal run reads the table only at `proverKeysG`. -/
lemma proveIdeal2_table_congrG {K : Type} [Fintype K] [DecidableEq K] (enc : K → ByteArray)
    (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows) (x : IdealTape2 st.params)
    (G G' : K → Bytes 4) (h : ∀ key ∈ proverKeysG Hs CrtGen.tables (st1 st) enc x.1, G key = G' key) :
    proveIdeal2 (Hs.withTable .h5 enc G) CrtGen.tables st r k x =
      proveIdeal2 (Hs.withTable .h5 enc G') CrtGen.tables st r k x := by
  refine proveIdeal2_h5_congr CrtGen.tables st r k hlab (fun k' hk =>
    ((Hs.agreeOff_withTable .h5 _ G k' hk).symm.trans (Hs.agreeOff_withTable .h5 _ G' k' hk))) x
    fun y hy => ?_
  rw [actInputs_withTable_h5G] at hy
  simp only [Hashes.withTable, ↓reduceIte]
  split
  · rename_i hy'
    have hk : hy'.choose ∈ proverKeysG Hs CrtGen.tables (st1 st) enc x.1 := by
      rw [mem_proverKeysG, hy'.choose_spec]; exact hy
    exact congrArg ba (h _ hk)
  · rfl

/-- **The verifier's `H₅` inputs on the final proof of the two-phase ideal run**, for the instance
the continuation picks, are active gate inputs of the tape. -/
theorem vIn5_proveIdeal2 (Hs' : Hashes) (hh : Hyp2 st r k) (s : Shared) (t : Pads st.params)
    (fb : Fallback st.params) {b : ByteArray} {y : Inst2} {sfx : ByteArray}
    (hb : (proveIdeal2 Hs' CrtGen.tables st r k ((s, t), fb)).2.2 = some (.ok b))
    (hk1 : k ((proveIdeal2 Hs' CrtGen.tables st r k ((s, t), fb)).1,
      (proveIdeal2 Hs' CrtGen.tables st r k ((s, t), fb)).2.1) = some (y, sfx)) :
    ∀ x ∈ vIn5 Hs CrtGen.tables (withInst st y) b, x ∈ actInputs Hs CrtGen.tables (st1 st) s t := by
  rcases hf : firstHit s.2.1 with _ | ⟨ctr, δ⟩
  · simp only [proveIdeal2, hf, Option.map_eq_some_iff] at hb
    obtain ⟨_, _, he⟩ := hb
    cases he
  · have hd : deltaOf s.2.1 = δ := by unfold deltaOf; rw [hf]; rfl
    simp only [proveIdeal2, hf] at hb hk1
    rw [hk1, Option.map_some, Option.some.injEq] at hb
    have hz := hh.hk _ _ _ hk1
    rw [idealCore_fields Hs' CrtGen.tables (withInst st y) (r ++ sfx) y.sys hz.hvals hz.hdeg hz.hd
      hz.hd' hz.hI hz.hsat, Except.ok.injEq] at hb
    subst hb
    intro x hx
    have := vIn5_simAssemble Hs CrtGen.tables (withInst st y) s ctr δ _ hf x hx
    rw [actInputs, qcolsTape, hd, correctionsOf_eq]
    exact this

lemma qcolsTape_eq_ad (Hs' : Hashes) (s : Shared) (ctr : ℕ) (δ : Bytes 16) (t : Pads st.params) :
    qcolsTape Hs (st1 st) s t = qcolsF Hs (st1 st) s (fieldsAd Hs' CrtGen.tables st r k s ctr δ t) := by
  rw [qcolsTape, qcolsF, correctionsOf_eq]
  rfl

variable {K : Type} [Fintype K] [DecidableEq K] (enc : K → ByteArray)
  (sk : Shared × PadsU st.params → Fin 312 → K)

/-- The candidates for `u_pre` in a two-phase run: zero (the prover's reads) and the guesses of
the queries of `QD` at the simulated output of the fields. -/
noncomputable def guesses2 (QD : Out2 → Shared → (K → Bytes 4) → Finset K) (G : K → Bytes 4)
    (s : Shared) (fb : Fallback st.params) (f : SimFields st.params) : Finset W128 :=
  insert W128.zero ((QD (simRun2 (Hs.withTable .h5 enc G) st r.size k ((s, f), fb)) s G).biUnion
    (guessOfG Hs CrtGen.tables (st1 st) enc s f))

set_option synthInstance.maxSize 1024 in
/-- **For a fixed shared tape, fallback block and table, a sibling input is read with probability
`≤ (q + 1)·2⁻¹²⁸`** (two phases): by the prover (`u_pre = 0`) or by one of `D`'s `q` queries (each
a guess of `u_pre` from the shared tape and the adaptive fields, `Θ` uniform given them). -/
theorem pr_bad2 (hh : Hyp2 st r k)
    (hsk : ∀ c e, enc (sk c e) = sibInput Hs CrtGen.tables (st1 st) c.1 (withSib c.2 fun _ => fun _ => 0) e)
    (QD : Out2 → Shared → (K → Bytes 4) → Finset K) {q : ℕ} (hq : ∀ o s G, (QD o s G).card ≤ q)
    (G : K → Bytes 4) (s : Shared) (fb : Fallback st.params) :
    pr (Pads st.params) (fun t => ∃ e, sk (s, dropSib t) e ∈ proverKeysG Hs CrtGen.tables (st1 st) enc (s, t) ∪
      QD (proveIdeal2 (Hs.withTable .h5 enc G) CrtGen.tables st r k ((s, t), fb)) s G) ≤
      (q + 1) / 2 ^ 128 := by
  obtain ⟨h1, -, hlb, h2⟩ := labelRows_sizes hh.hlr
  have hlab := hh.hlab
  let H := Hs.withTable .h5 enc G
  let F : Pads st.params → SimFields st.params × Bytes (labelBytes st.params) := fun t =>
    (fieldsAd H CrtGen.tables st r k s (hit2 s).1 (hit2 s).2 t, t.2.1)
  let S := guesses2 Hs st r k enc QD G s fb
  have e1 : pr (Pads st.params) (fun t => ∃ e, sk (s, dropSib t) e ∈
      proverKeysG Hs CrtGen.tables (st1 st) enc (s, t) ∪
        QD (proveIdeal2 H CrtGen.tables st r k ((s, t), fb)) s G) ≤
      pr (Pads st.params) (fun t => thetaW st.params (F t).2 ∈ S (F t).1) := by
    refine pr_mono fun t ht => ?_
    obtain ⟨e, he⟩ := ht
    have hsib : enc (sk (s, dropSib t) e) = sibInput Hs CrtGen.tables (st1 st) s t e := by
      rw [hsk]; rfl
    show thetaW st.params t.2.1 ∈ S _
    rw [← uPre_eq_thetaW hh.hlr]
    unfold S guesses2
    rw [Finset.mem_insert]
    rw [Finset.mem_union] at he
    rcases he with he | he
    · left
      rw [mem_proverKeysG, hsib] at he
      exact uPre_zero_of_sib_mem Hs CrtGen.tables (st1 st) hlab s t e he
    · right
      rw [Finset.mem_biUnion]
      refine ⟨_, by rw [← proveIdeal2_eq_simRun2 H CrtGen.tables st r k hh.hk hh.hr]; exact he,
        mem_guessOfG Hs CrtGen.tables (st1 st) enc (e := e) ?_⟩
      rw [hsib, sibInput_eq Hs CrtGen.tables (st1 st) hlab, qcolsTape_eq_ad Hs st r k H]
  have e2 : pr (Pads st.params) (fun t => thetaW st.params (F t).2 ∈ S (F t).1) =
      pr (SimFields st.params × Bytes (labelBytes st.params))
        (fun y => thetaW st.params y.2 ∈ S y.1) := by
    have := (upush_fieldsAdθ H CrtGen.tables st r k s (hit2 s).1 (hit2 s).2 maskInvOk_tables hh.hnm
      hh.hr) (fun y => thetaW st.params y.2 ∈ S y.1)
    rw [abs_nonpos_iff, sub_eq_zero] at this
    exact this
  have hS : ∀ f, (S f).card ≤ q + 1 := fun f => by
    unfold S guesses2
    refine (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ?_)
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ key ∈ QD (simRun2 H st r.size k ((s, f), fb)) s G,
          (guessOfG Hs CrtGen.tables (st1 st) enc s f key).card
        ≤ ∑ _key ∈ QD (simRun2 H st r.size k ((s, f), fb)) s G, 1 :=
          Finset.sum_le_sum fun key _ => card_guessOfG_le Hs CrtGen.tables (st1 st) enc s f key
      _ ≤ q := by rw [Finset.sum_const, smul_eq_mul, mul_one]; exact hq _ _ _
  have e3 : pr (SimFields st.params × Bytes (labelBytes st.params))
      (fun y => thetaW st.params y.2 ∈ S y.1) ≤
      ((q + 1 : ℕ) : ℝ) / Fintype.card (Bytes (labelBytes st.params)) := by
    rw [← pr_equiv (Equiv.prodComm (Bytes (labelBytes st.params)) (SimFields st.params))]
    exact pr_mem_indep_le (thetaW st.params) (thetaW_injective hh.hlr) S hS
  have hc : ((2 ^ (8 * labelBytes st.params) : ℕ) : ℝ) = 2 ^ 128 := by rw [hlb]; norm_num
  rw [Prob.card_bytes, hc] at e3
  refine (e1.trans (e2.le.trans e3)).trans (le_of_eq ?_)
  push_cast
  norm_num

set_option synthInstance.maxSize 1024 in
/-- **`LabHyp` in the ROM for the two-phase run, for a distinguisher that also reads the shared
tape** (any table layout of `H₅`, a fixed fallback block). -/
theorem lab2_hyp (kf : (K → Bytes 4) → Cont2) (hh : ∀ G, Hyp2 st r (kf G))
    (hsk : ∀ c e, enc (sk c e) = sibInput Hs CrtGen.tables (st1 st) c.1 (withSib c.2 fun _ => fun _ => 0) e)
    (hkey : ∀ c e, keyOf enc (sk c e) = sk c e) (fb : Fallback st.params)
    (D : Out2 → Shared → (K → Bytes 4) → Prop) (QD : Out2 → Shared → (K → Bytes 4) → Finset K)
    (hA : ∀ (t : IdealTape st.params) G G', (∀ key ∈ proverKeysG Hs CrtGen.tables (st1 st) enc t ∪
        QD (proveIdeal2 (Hs.withTable .h5 enc G) CrtGen.tables st r (kf G) (t, fb)) t.1 G, G key = G' key) →
      (D (proveIdeal2 (Hs.withTable .h5 enc G) CrtGen.tables st r (kf G) (t, fb)) t.1 G ↔
        D (proveIdeal2 (Hs.withTable .h5 enc G') CrtGen.tables st r (kf G') (t, fb)) t.1 G'))
    {q : ℕ} (hq : ∀ o s G, (QD o s G).card ≤ q) :
    |pr (IdealTape st.params × (K → Bytes 4)) (fun x =>
        D (proveIdeal2 (Hs.withTable .h5 enc x.2) CrtGen.tables st r (kf x.2)
          (fillSib (Hs.withTable .h5 enc x.2) CrtGen.tables (st1 st) x.1, fb)) x.1.1 x.2) -
      pr (IdealTape st.params × (K → Bytes 4)) (fun x =>
        D (proveIdeal2 (Hs.withTable .h5 enc x.2) CrtGen.tables st r (kf x.2) (x.1, fb)) x.1.1 x.2)| ≤
      (q + 1) / 2 ^ 128 := by
  let A : IdealTape st.params → (K → Bytes 4) → Prop := fun t G =>
    D (proveIdeal2 (Hs.withTable .h5 enc G) CrtGen.tables st r (kf G) (t, fb)) t.1 G
  let E2 : ((Shared × PadsU st.params) × (K → Bytes 4)) × Sib ≃
      IdealTape st.params × (K → Bytes 4) :=
    { toFun := fun y => ((y.1.1.1, withSib y.1.1.2 y.2), y.1.2)
      invFun := fun x => (((x.1.1, dropSib x.1.2), x.2), x.1.2.2.2.2.2.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let E3 : (Shared × PadsU st.params) × ((K → Bytes 4) × Sib) ≃
      IdealTape st.params × (K → Bytes 4) :=
    { toFun := fun y => ((y.1.1, withSib y.1.2 y.2.2), y.2.1)
      invFun := fun x => ((x.1.1, dropSib x.1.2), (x.2, x.1.2.2.2.2.2.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have e1 : pr (IdealTape st.params × (K → Bytes 4)) (fun x =>
      D (proveIdeal2 (Hs.withTable .h5 enc x.2) CrtGen.tables st r (kf x.2)
        (fillSib (Hs.withTable .h5 enc x.2) CrtGen.tables (st1 st) x.1, fb)) x.1.1 x.2) =
      pr ((Shared × PadsU st.params) × (K → Bytes 4)) (fun x =>
        A (fillSib (Hs.withTable .h5 enc x.2) CrtGen.tables (st1 st)
          (x.1.1, withSib x.1.2 fun _ => fun _ => 0)) x.2) := by
    rw [← pr_equiv E2, ← pr_prod_fst (β := Sib) (fun x : (Shared × PadsU st.params) ×
      (K → Bytes 4) => A (fillSib (Hs.withTable .h5 enc x.2) CrtGen.tables (st1 st)
        (x.1.1, withSib x.1.2 fun _ => fun _ => 0)) x.2)]
    refine pr_congr fun y => ?_
    show D (proveIdeal2 (Hs.withTable .h5 enc y.1.2) CrtGen.tables st r (kf y.1.2)
        (fillSib (Hs.withTable .h5 enc y.1.2) CrtGen.tables (st1 st) (y.1.1.1, withSib y.1.1.2 y.2),
          fb)) y.1.1.1 y.1.2 ↔ _
    rw [fillSib_withSib CrtGen.tables (st1 st) _ y.1.1.1 y.1.1.2 y.2 fun _ => fun _ => 0]
    rfl
  have e2 : pr (IdealTape st.params × (K → Bytes 4)) (fun x =>
      D (proveIdeal2 (Hs.withTable .h5 enc x.2) CrtGen.tables st r (kf x.2) (x.1, fb)) x.1.1 x.2) =
      pr ((Shared × PadsU st.params) × ((K → Bytes 4) × Sib))
        (fun x => A (x.1.1, withSib x.1.2 x.2.2) x.2.1) :=
    (pr_equiv E3 _).symm
  rw [e1, e2]
  refine (lab_romG Hs CrtGen.tables (st1 st) enc sk hsk hkey A
    (fun t G => proverKeysG Hs CrtGen.tables (st1 st) enc t ∪
      QD (proveIdeal2 (Hs.withTable .h5 enc G) CrtGen.tables st r (kf G) (t, fb)) t.1 G)
    fun t G G' hG => hA t G G' hG).trans ?_
  let E : (K → Bytes 4) × IdealTape st.params ≃
      (Shared × PadsU st.params) × ((K → Bytes 4) × Sib) :=
    { toFun := fun y => ((y.2.1, dropSib y.2.2), (y.1, y.2.2.2.2.2.2.2.2))
      invFun := fun x => (x.2.1, (x.1.1, withSib x.1.2 x.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv E]
  refine pr_prod_le _ fun G => pr_prod_le _ fun s => ?_
  exact pr_bad2 Hs st r (kf G) enc sk (hh G) hsk QD hq G s fb

end H6

/-- **H6 with the tables** (two phases): the sibling answers recomputed from the `H₅` table against
uniform ones, for a distinguisher that reads the `H₅` table at `q₅` keys (and sees the other
tables, the grinding answers through the programmed `H₂³` table, and the fallback block through
the output). The simulator's recomputation reads `H₅` only at the prover's own active inputs
(`vIn5_proveIdeal2`), so it adds no reads. -/
theorem zk2_h6 (Hb : Hashes) (st : Statement) (r : ByteArray) (kf : Tab5F → Cont2)
    (hHb : HashesWF Hb) (hh : ∀ G5, Hyp2 st r (kf G5))
    (QK5 : Tab5F → Finset (Bytes 37))
    (hQK5 : ∀ G5 G5', (∀ key ∈ QK5 G5, G5 key = G5' key) → kf G5 = kf G5')
    {qk5 : ℕ} (hqk5 : ∀ G5, (QK5 G5).card ≤ qk5)
    (D : Out2 → Tab3 → Tab2G st.params → Tab5F → Prop)
    (Q5 : Out2 → Tab3 → Tab2G st.params → Tab5F → Finset (Bytes 37))
    (hQ5 : ∀ o G3 G2 G5 G5', (∀ k ∈ Q5 o G3 G2 G5, G5 k = G5' k) →
      (D o G3 G2 G5 ↔ D o G3 G2 G5'))
    {q5 : ℕ} (hq5 : ∀ o G3 G2 G5, (Q5 o G3 G2 G5).card ≤ q5) :
    |pr (IdealTape2 st.params × Vis2 st.params) (fun c =>
        Dp2 Hb CrtGen.tables st (kf c.2.2.2) D (proveIdeal2 (recB Hb (st1 st) r c.2.1 c.2.2.2) CrtGen.tables
          st r (kf c.2.2.2) (fillSib (recB Hb (st1 st) r c.2.1 c.2.2.2) CrtGen.tables (st1 st) c.1.1, c.1.2))
          c.1.1.1.2.1 c.2) -
      pr (IdealTape2 st.params × Vis2 st.params) (fun c =>
        Dp2 Hb CrtGen.tables st (kf c.2.2.2) D (proveIdeal2 (recB Hb (st1 st) r c.2.1 c.2.2.2) CrtGen.tables
          st r (kf c.2.2.2) c.1) c.1.1.1.2.1 c.2)| ≤
      (q5 + qk5 + 1) / 2 ^ 128 := by
  have hlab := (hh fun _ => 0).hlab
  let E6 : (Tab3 × Tab2G st.params) × (Fallback st.params × (IdealTape st.params × Tab5F)) ≃
      IdealTape2 st.params × Vis2 st.params :=
    { toFun := fun c => ((c.2.2.1, c.2.1), (c.1.1, (c.1.2, c.2.2.2)))
      invFun := fun c => ((c.2.1, c.2.2.1), (c.1.2, (c.1.1, c.2.2.2)))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv E6, ← pr_equiv E6]
  refine abs_pr_prod_sub_le _ _ fun a => abs_pr_prod_sub_le _ _ fun fb => ?_
  obtain ⟨G3, G2⟩ := a
  set base := (Hb.withTable .h3 (seedInput ((st1 st).mu1 Hb)
    (r.extract 0 (st1 st).params.witnessBytes)) G3).withTable .h23 (enc2 (st1 st).params)
      (fun _ => 0) with hbase
  have a1 := Hb.agreeOff_withTable .h3 (seedInput ((st1 st).mu1 Hb)
    (r.extract 0 (st1 st).params.witnessBytes)) G3
  have a2 := (Hb.withTable .h3 (seedInput ((st1 st).mu1 Hb)
    (r.extract 0 (st1 st).params.witnessBytes)) G3).agreeOff_withTable .h23
      (enc2 (st1 st).params) (fun _ => 0)
  have hbwf : HashesWF base := (hHb.withTable .h3 _ G3).withTable .h23 _ _
  let sk : Shared × PadsU st.params → Fin 312 → Bytes 37 := fun c e =>
    blk 37 (sibInput base CrtGen.tables (st1 st) c.1 (withSib c.2 fun _ => fun _ => 0) e)
  have hsk : ∀ c e, enc5 (sk c e) =
      sibInput base CrtGen.tables (st1 st) c.1 (withSib c.2 fun _ => fun _ => 0) e :=
    fun c e => ba_blk_of_size (sibInput_size base CrtGen.tables (st1 st) hbwf _ _ e)
  have hkey : ∀ c e, keyOf enc5 (sk c e) = sk c e :=
    fun c e => keyOf_eq (fun a b h => ba_injective h) _
  have hv5 : ∀ (G : Tab5F) (st' : Statement), (st' = st1 st ∨ ∃ y, st' = withInst st y) →
      vIn5 (rec5 Hb G) CrtGen.tables st' = vIn5 base CrtGen.tables st' := by
    intro G st' _
    have a0 := Hb.agreeOff_withTable .h5 enc5 G
    refine vIn5_congr CrtGen.tables st' ?_ ?_
    · exact (a0.mu1 (by decide) (by decide) st').symm.trans
        ((a1.mu1 (by decide) (by decide) st').trans (a2.mu1 (by decide) (by decide) st'))
    · exact (a0 .h4 (by decide)).symm.trans ((a1 .h4 (by decide)).trans (a2 .h4 (by decide)))
  let QD : Out2 → Shared → Tab5F → Finset (Bytes 37) := fun o s G5 =>
    Q5 o G3 (simTab2 Hb CrtGen.tables st (kf G5) G5 o s.2.1 G2) G5 ∪ QK5 G5
  have hA : ∀ (t : IdealTape st.params) (G G' : Tab5F), (∀ key ∈ proverKeysG base CrtGen.tables
      (st1 st) enc5 t ∪ QD (proveIdeal2 (base.withTable .h5 enc5 G) CrtGen.tables st r (kf G) (t, fb))
        t.1 G, G key = G' key) →
      (Dp2 Hb CrtGen.tables st (kf G) D (proveIdeal2 (base.withTable .h5 enc5 G) CrtGen.tables st r (kf G)
          (t, fb)) t.1.2.1 (G3, G2, G) ↔
        Dp2 Hb CrtGen.tables st (kf G') D (proveIdeal2 (base.withTable .h5 enc5 G') CrtGen.tables st r (kf G')
          (t, fb)) t.1.2.1 (G3, G2, G')) := by
    rintro ⟨s0, t0⟩ G G' hG
    have hK : kf G' = kf G := (hQK5 G G' fun key hk =>
      hG key (Finset.mem_union_right _ (Finset.mem_union_right _ hk))).symm
    rw [hK]
    have hp := proveIdeal2_table_congrG base st r (kf G) enc5 hlab ((s0, t0), fb) G G'
      fun key hk => hG key (Finset.mem_union_left _ hk)
    have hpre : outPre2 Hb CrtGen.tables st (kf G) G
        (proveIdeal2 (base.withTable .h5 enc5 G) CrtGen.tables st r (kf G) ((s0, t0), fb)) =
        outPre2 Hb CrtGen.tables st (kf G) G'
          (proveIdeal2 (base.withTable .h5 enc5 G) CrtGen.tables st r (kf G) ((s0, t0), fb)) := by
      unfold outPre2
      rcases hb : (proveIdeal2 (base.withTable .h5 enc5 G) CrtGen.tables st r (kf G) ((s0, t0), fb)).2.2 with
        _ | e | b
      · rfl
      · rfl
      rcases hk1 : kf G ((proveIdeal2 (base.withTable .h5 enc5 G) CrtGen.tables st r (kf G) ((s0, t0), fb)).1,
        (proveIdeal2 (base.withTable .h5 enc5 G) CrtGen.tables st r (kf G) ((s0, t0), fb)).2.1) with _ | ⟨y, sfx⟩
      · rfl
      dsimp only
      have hag : (rec5 Hb G).AgreeOff .h5 (rec5 Hb G') :=
        Hashes.AgreeOff.withTable_same (k := .h5) (Hs := Hb) (Hs' := Hb) (fun _ _ => rfl) enc5
          enc5 G G'
      refine vPre_h5_congr hag CrtGen.tables (withInst st y) b fun x hx => ?_
      rw [hv5 G (withInst st y) (Or.inr ⟨y, rfl⟩)] at hx
      have hx' : x ∈ actInputs base CrtGen.tables (st1 st) s0 t0 :=
        vIn5_proveIdeal2 base st r (kf G) (base.withTable .h5 enc5 G) (hh G) s0 t0 fb hb hk1 x hx
      simp only [rec5, Hashes.withTable, ↓reduceIte]
      split
      · rename_i hy
        have hk : hy.choose ∈ proverKeysG base CrtGen.tables (st1 st) enc5 (s0, t0) := by
          rw [mem_proverKeysG, hy.choose_spec]; exact hx'
        exact congrArg ba (hG _ (Finset.mem_union_left _ hk))
      · rfl
    have hX : simTab2 Hb CrtGen.tables st (kf G) G'
        (proveIdeal2 (base.withTable .h5 enc5 G') CrtGen.tables st r (kf G) ((s0, t0), fb)) s0.2.1 G2 =
        simTab2 Hb CrtGen.tables st (kf G) G
          (proveIdeal2 (base.withTable .h5 enc5 G) CrtGen.tables st r (kf G) ((s0, t0), fb)) s0.2.1 G2 := by
      unfold simTab2
      rw [← hp, ← hpre]
    show D (proveIdeal2 (base.withTable .h5 enc5 G) CrtGen.tables st r (kf G) ((s0, t0), fb)) G3
        (simTab2 Hb CrtGen.tables st (kf G) G
          (proveIdeal2 (base.withTable .h5 enc5 G) CrtGen.tables st r (kf G) ((s0, t0), fb)) s0.2.1 G2) G ↔
      D (proveIdeal2 (base.withTable .h5 enc5 G') CrtGen.tables st r (kf G) ((s0, t0), fb)) G3
        (simTab2 Hb CrtGen.tables st (kf G) G'
          (proveIdeal2 (base.withTable .h5 enc5 G') CrtGen.tables st r (kf G) ((s0, t0), fb)) s0.2.1 G2) G'
    rw [hX, ← hp]
    exact hQ5 _ G3 _ G G' fun key hk => hG key (Finset.mem_union_right _ (Finset.mem_union_left _ hk))
  have hc : ((q5 + qk5 : ℕ) + 1 : ℝ) / 2 ^ 128 = (q5 + qk5 + 1) / 2 ^ 128 := by push_cast; ring
  rw [← hc]
  exact lab2_hyp base st r enc5 sk kf hh hsk hkey fb
    (fun o (s : Shared) G5 => Dp2 Hb CrtGen.tables st (kf G5) D o s.2.1 (G3, G2, G5)) QD hA
    (fun o s G => (card_union_le _ _).trans (add_le_add (hq5 _ _ _ _) (hqk5 _)))

end VoleMole.ZK.Sim
