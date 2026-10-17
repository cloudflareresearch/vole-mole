import VoleMole.ZK.TwoPhase

/-!
# The two-phase tape hypothesis from one assumption per hop (`lean/docs/zk.md` §7.5, §10.1)

`ZK/Hops.lean` for the two-phase run of `ZK/TwoPhase.lean` (PomFRIT: step 1 with the witness
prefix `r`, then step 2 for the instance and suffix a continuation `k` picks from step 1's output).
The tape of a real two-phase run (`tapeOf2`) is `tapeAt` of step 1 with the grinding answers at the
points of the picked instance, and a fallback block (step 1's output) that the ideal run outputs
only when no grinding answer is accepted.

**`tapeHyp2_of_hops`**: from the hop hypotheses `HopHyps2` (H1 for step 1's seed input, the grinding
answers at the prefix the continuation determines, BAVC hiding `HideHyp`, and H6 through the ideal
two-phase run, `LabHyp2`), the two-phase tape hypothesis `TapeHyp2` holds with
`ε_rho + ε_grind + ε_abort + ε_bavc + ε_lab`. The extra term `ε_abort = noHitProb` is the
probability that none of the `2³²` uniform grinding answers is accepted: only then does the ideal
run read the fallback block, which is real in the real run and uniform on the ideal tape (exact
value `(|Aᶜ|/2¹²⁸)^{2³²}` by `Grinding.card_noHit`).

`ZK/TwoPhaseRO.lean` and `ZK/TwoPhaseIC.lean` run the same hybrids in the random-oracle and
ideal-cipher model with the tables visible (`zk2_rom_ic_h23_num`), where the abort term is inside
`Pr[GrindBad]`.
-/

open Finset

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy

-- The statements hold for any CTR PRG (`HasPrg`, `Verifier/Prg.lean`), AES included.
variable [VoleMole.Verifier.HasPrg]
set_option linter.unusedSectionVars false

/-- **The abort term**: the probability that no uniform grinding answer is accepted. -/
noncomputable def noHitProb : ℝ := pr Grind (fun g => firstHit g = none)

section TwoPhase

variable (Hs : Hashes) (T : CrtTables) (st : Statement) (r : ByteArray) (k : Cont2)

/-- The grinding prefix of a two-phase run whose step 1 has the root seed and `iv_pre` `x`: the
instance and suffix the continuation picks from step 1's output. -/
def pre2 (x : Bytes 16 × Bytes 16) : ByteArray :=
  let s := pendAt Hs T (st1 st) r x
  let y := (k (s.proof, s.chal1)).getD (default, .empty)
  realPre Hs (withInst st y.1) s (r ++ y.2)

/-- The fallback block of a two-phase run whose step 1 has the root seed and `iv_pre` `x`. -/
def fb2 (x : Bytes 16 × Bytes 16) : Fallback st.params :=
  (blk _ (pendAt Hs T (st1 st) r x).proof, blk 136 (pendAt Hs T (st1 st) r x).chal1)

/-- **The two-phase H6 hypothesis**: on a uniform tape, the ideal two-phase run with the sibling
answers the tape determines is `ε`-close to the one with uniform sibling answers. -/
def LabHyp2 (ε : ℝ) : Prop :=
  Close ε (fun t : IdealTape2 st.params => proveIdeal2 Hs T st r k (fillSib Hs T (st1 st) t.1, t.2))
    (proveIdeal2 Hs T st r k)

/-- **The hop hypotheses of a two-phase run**, with their errors. -/
structure HopHyps2 (εrho εgrind εbavc εlab : ℝ) : Prop where
  rho : H3Hyp Hs ((st1 st).mu1 Hs) r εrho
  grind : GrindHyp Hs (pre2 Hs T st r k) εgrind
  bavc : HideHyp st.params εbavc
  lab : LabHyp2 Hs T st r k εlab

lemma tapeOf2_eq (hHs : HashesWF Hs) (rho : ByteArray) :
    tapeOf2 Hs T st r k rho =
      (tapeAt Hs T st.params (pendAt Hs T (st1 st) r (h3Seed Hs ((st1 st).mu1 Hs) r rho))
        (realGrind Hs (pre2 Hs T st r k (h3Seed Hs ((st1 st).mu1 Hs) r rho))),
        fb2 Hs T st r (h3Seed Hs ((st1 st).mu1 Hs) r rho)) := by
  have e : step1 Hs T st r rho = pendAt Hs T (st1 st) r (h3Seed Hs ((st1 st).mu1 Hs) r rho) :=
    voleGen_eq_pendAt Hs hHs T (st1 st) r rho
  simp only [tapeOf2, pre2, fb2, e]

lemma proveIdeal2_none {t : IdealTape2 st.params} (hg : firstHit t.1.1.2.1 = none) :
    proveIdeal2 Hs T st r k t =
      (ba t.2.1, ba t.2.2, (k (ba t.2.1, ba t.2.2)).map fun _ => .error "grinding failed") := by
  simp only [proveIdeal2, hg]

/-- With an accepted grinding answer the ideal run does not read the fallback block. -/
lemma proveIdeal2_fb {t : IdealTape st.params} {ctr : ℕ} {d : Bytes 16}
    (hg : firstHit t.1.2.1 = some (ctr, d)) (fb fb' : Fallback st.params) :
    proveIdeal2 Hs T st r k (t, fb) = proveIdeal2 Hs T st r k (t, fb') := by
  simp only [proveIdeal2, hg]

/-- The real run's sibling answers are the ones its tape determines, seen through the ideal
two-phase run. -/
theorem real_fillSib2 (hHs : HashesWF Hs) (hbavc : BAVCComplete)
    (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows) (x : Bytes 16 × Bytes 16)
    (g : Grind) (fb : Fallback st.params) :
    proveIdeal2 Hs T st r k
        (fillSib Hs T (st1 st) (tapeAt Hs T st.params (pendAt Hs T (st1 st) r x) g), fb) =
      proveIdeal2 Hs T st r k (tapeAt Hs T st.params (pendAt Hs T (st1 st) r x) g, fb) := by
  have hg1 : (tapeAt Hs T st.params (pendAt Hs T (st1 st) r x) g).1.2.1 = g := rfl
  rcases hg : firstHit g with _ | ⟨ctr, d⟩
  · rw [proveIdeal2_none Hs T st r k (by rw [fillSib_fst, hg1, hg]),
      proveIdeal2_none Hs T st r k (by rw [hg1, hg])]
  · exact congrArg (fun t => proveIdeal2 Hs T st r k (t, fb))
      (fillSib_tapeAt_eq Hs T (st1 st) hHs hbavc hlab (pendAt Hs T (st1 st) r x) rfl (size_ba _)
        (size_ba _) hg)

/-- The ideal prover's step 1 reads the shared tape through the public values and fields. -/
lemma idealPhase1_congr {s s' : Shared} {ctr : ℕ} {d : Bytes 16} (t : Pads st.params)
    (h1 : pubOf Hs (st1 st) s d = pubOf Hs (st1 st) s' d)
    (h2 : publicFields s ctr d = publicFields s' ctr d) :
    idealPhase1 Hs T (st1 st) r s ctr d t = idealPhase1 Hs T (st1 st) r s' ctr d t := by
  simp only [idealPhase1, tUt, tC1, tF1, tF0, h1, h2]

/-- **The seed slots past the opened ones do not matter** (two phases). -/
theorem proveIdeal2_fillSib_zeroTail (a : Bytes 16) (g : Grind) (c : Fin BAVC.tau → Bytes 32)
    (sd : Fin 105 → Bytes 16) (t : Pads st.params) (fb : Fallback st.params) :
    proveIdeal2 Hs T st r k (fillSib Hs T (st1 st) ((a, g, c, zeroTail (ba (deltaOf g)) sd), t), fb) =
      proveIdeal2 Hs T st r k (fillSib Hs T (st1 st) ((a, g, c, sd), t), fb) := by
  have hf : ∀ sd', fillSib Hs T (st1 st) ((a, g, c, sd'), t) =
      ((a, g, c, sd'), withSib (dropSib t) (sibOf Hs T (st1 st) (a, g, c, sd') t)) := fun _ => rfl
  rw [hf, hf]
  rcases hg : firstHit g with _ | ⟨ctr, d⟩
  · rw [proveIdeal2_none Hs T st r k (by rw [tuple_grind, hg]),
      proveIdeal2_none Hs T st r k (by rw [tuple_grind, hg])]
  · have hdel : deltaOf g = d := by simp only [deltaOf, hg, Option.map_some, Option.getD_some]
    have hsib : sibOf Hs T (st1 st) (a, g, c, zeroTail (ba (deltaOf g)) sd) t =
        sibOf Hs T (st1 st) (a, g, c, sd) t := by
      rw [sibOf_eq, sibOf_eq, hdel, pubOf_tuple, pubOf_tuple, openingOf_zeroTail]
    rw [hsib]
    have e1 : ∀ (s' : Shared) (t' : Pads st.params), s'.2.1 = g →
        proveIdeal2 Hs T st r k ((s', t'), fb) =
          ((idealPhase1 Hs T (st1 st) r s' ctr d t').1, (idealPhase1 Hs T (st1 st) r s' ctr d t').2,
            (k (idealPhase1 Hs T (st1 st) r s' ctr d t')).map fun x =>
              idealCore Hs T (withInst st x.1) (r ++ x.2) s' ctr d t') := by
      intro s' t' hs'
      simp only [proveIdeal2, hs', hg]
    have hpub : ∀ st' : Statement, pubOf Hs st' (a, g, c, zeroTail (ba d) sd) d =
        pubOf Hs st' (a, g, c, sd) d := fun st' => by
      rw [pubOf_tuple, pubOf_tuple, openingOf_zeroTail]
    have hpf : publicFields (a, g, c, zeroTail (ba d) sd) ctr d = publicFields (a, g, c, sd) ctr d := by
      rw [publicFields_tuple, publicFields_tuple, openingOf_zeroTail]
    rw [e1 _ _ (tuple_grind _ _ _ _), e1 _ _ (tuple_grind _ _ _ _), hdel,
      idealPhase1_congr Hs T st r (s := (a, g, c, zeroTail (ba d) sd)) (s' := (a, g, c, sd)) _
        (hpub _) hpf]
    have hC : ∀ x : Inst2 × ByteArray,
        idealCore Hs T (withInst st x.1) (r ++ x.2) (a, g, c, zeroTail (ba d) sd) ctr d
          (withSib (dropSib t) (sibOf Hs T (st1 st) (a, g, c, sd) t)) =
        idealCore Hs T (withInst st x.1) (r ++ x.2) (a, g, c, sd) ctr d
          (withSib (dropSib t) (sibOf Hs T (st1 st) (a, g, c, sd) t)) :=
      fun x => idealCore_congr Hs T (withInst st x.1) (r ++ x.2) _ (hpub _) hpf
    simp only [hC]

/-! ## The hybrids -/

/-- Uniform root seed and `iv_pre`, the real grinding answers and fallback block. -/
def hyb1' (x : Bytes 16 × Bytes 16) : Out2 :=
  proveIdeal2 Hs T st r k (tapeAt Hs T st.params (pendAt Hs T (st1 st) r x)
    (realGrind Hs (pre2 Hs T st r k x)), fb2 Hs T st r x)

/-- Uniform root seed, `iv_pre` and grinding answers, the real fallback block. -/
def hyb2' (y : Bytes 16 × Bytes 16 × Grind) : Out2 :=
  proveIdeal2 Hs T st r k (tapeAt Hs T st.params (pendAt Hs T (st1 st) r (y.1, y.2.1)) y.2.2,
    fb2 Hs T st r (y.1, y.2.1))

/-- Uniform root seed, `iv_pre`, grinding answers and fallback block. -/
def hyb2'' (y : Bytes 16 × ((Bytes 16 × Grind) × Fallback st.params)) : Out2 :=
  proveIdeal2 Hs T st r k (tapeAt Hs T st.params (pendAt Hs T (st1 st) r (y.1, y.2.1.1)) y.2.1.2,
    y.2.2)

/-- The hidden part from `hid`, the sibling answers recomputed. -/
def hyb3' (b : (Bytes 16 × Grind) × Fallback st.params) (hid : Hidden st.params) : Out2 :=
  proveIdeal2 Hs T st r k
    (fillSib Hs T (st1 st) (tapeOfHidden b.1.1 b.1.2 hid fun _ => fun _ => 0), b.2)

theorem hop2_h1 (hHs : HashesWF Hs) {ε : ℝ} (h : H3Hyp Hs ((st1 st).mu1 Hs) r ε) :
    Close ε (fun ρ : Bytes 16 => proveIdeal2 Hs T st r k (tapeOf2 Hs T st r k (ba ρ)))
      (hyb1' Hs T st r k) :=
  (h.map (hyb1' Hs T st r k)).congr (fun ρ => by rw [tapeOf2_eq Hs T st r k hHs]; rfl)
    fun _ => rfl

theorem hop2_grind {ε : ℝ} (h : GrindHyp Hs (pre2 Hs T st r k) ε) :
    Close ε (hyb1' Hs T st r k) (hyb2' Hs T st r k) :=
  (h.map (hyb2' Hs T st r k)).congr (fun _ => rfl) fun _ => rfl

theorem hop2_abort :
    Close noHitProb (hyb2' Hs T st r k) (hyb2'' Hs T st r k) := by
  -- Add the (unused) uniform fallback block, then replace the real one where it is not read.
  have e1 : Close 0 (fun y : Bytes 16 × ((Bytes 16 × Grind) × Fallback st.params) =>
      hyb2' Hs T st r k (y.1, y.2.1)) (hyb2' Hs T st r k) :=
    Close.prod_right (X := fun (seed : Bytes 16) (b : (Bytes 16 × Grind) × Fallback st.params) =>
        hyb2' Hs T st r k (seed, b.1)) (Y := fun (seed : Bytes 16) (b : Bytes 16 × Grind) =>
        hyb2' Hs T st r k (seed, b)) fun seed =>
      close_prod_fst (X := fun b : Bytes 16 × Grind => hyb2' Hs T st r k (seed, b))
  have e2 := Close.of_agree (X := fun y : Bytes 16 × ((Bytes 16 × Grind) × Fallback st.params) =>
      hyb2' Hs T st r k (y.1, y.2.1)) (Y := hyb2'' Hs T st r k)
    (fun y => firstHit y.2.1.2 = none) fun y hy => by
      obtain ⟨⟨ctr, d⟩, hg⟩ := Option.ne_none_iff_exists'.1 hy
      exact proveIdeal2_fb Hs T st r k
        (t := tapeAt Hs T st.params (pendAt Hs T (st1 st) r (y.1, y.2.1.1)) y.2.1.2) hg _ _
  have hp : pr (Bytes 16 × ((Bytes 16 × Grind) × Fallback st.params))
      (fun y => firstHit y.2.1.2 = none) = noHitProb := by
    rw [pr_prod_snd (fun b : (Bytes 16 × Grind) × Fallback st.params => firstHit b.1.2 = none),
      pr_prod_fst (fun b : Bytes 16 × Grind => firstHit b.2 = none),
      pr_prod_snd (fun g : Grind => firstHit g = none)]
    rfl
  rw [hp] at e2
  exact (e1.symm.trans e2).mono (by norm_num)

theorem hop2_hide (hHs : HashesWF Hs) (hbavc : BAVCComplete)
    (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows) {ε : ℝ}
    (h : HideHyp st.params ε) :
    Close ε (hyb2'' Hs T st r k) (fun y : Hidden st.params × ((Bytes 16 × Grind) × Fallback st.params) =>
      hyb3' Hs T st r k y.2 (hiddenIdeal (ba (deltaOf y.2.1.2)) y.1)) := by
  let ivOf : Bytes 16 → ByteArray := fun ivPre => Hs.hash .h4 ((ba ivPre ++ (st1 st).mu1 Hs).push 4)
  have hb : ∀ b : (Bytes 16 × Grind) × Fallback st.params, Close ε
      (fun seed : Bytes 16 =>
        hyb3' Hs T st r k b (hiddenOut st.params (ivOf b.1.1) (ba (deltaOf b.1.2)) seed))
      (fun hid : Hidden st.params => hyb3' Hs T st r k b (hiddenIdeal (ba (deltaOf b.1.2)) hid)) :=
    fun b => (h (ivOf b.1.1) (deltaOf b.1.2) (hHs .h4 _)).map (hyb3' Hs T st r k b)
  refine (Close.prod_left (X := fun (seed : Bytes 16) (b : (Bytes 16 × Grind) × Fallback st.params) =>
      hyb3' Hs T st r k b (hiddenOut st.params (ivOf b.1.1) (ba (deltaOf b.1.2)) seed))
    (Y := fun (hid : Hidden st.params) (b : (Bytes 16 × Grind) × Fallback st.params) =>
      hyb3' Hs T st r k b (hiddenIdeal (ba (deltaOf b.1.2)) hid)) hb).congr (fun y => ?_)
    fun _ => rfl
  rw [hyb2'', ← real_fillSib2 Hs T st r k hHs hbavc hlab,
    fillSib_tapeAt Hs T (st1 st) r y.1 y.2.1.1 y.2.1.2, pendAt_iv]
  rfl

lemma hyb3'_zeroTail (b : (Bytes 16 × Grind) × Fallback st.params) (hid : Hidden st.params) :
    hyb3' Hs T st r k b (hiddenIdeal (ba (deltaOf b.1.2)) hid) = hyb3' Hs T st r k b hid := by
  -- Destructured, so that the kernel never compares two projections of different tuples.
  obtain ⟨⟨a, g⟩, fb⟩ := b
  obtain ⟨c, sd, u⟩ := hid
  have e1 : tapeOfHidden a g (hiddenIdeal (ba (deltaOf g)) (c, sd, u)) (fun _ => fun _ => 0) =
      ((a, g, c, zeroTail (ba (deltaOf g)) sd), withSib u fun _ => fun _ => 0) := rfl
  have e2 : tapeOfHidden a g (c, sd, u) (fun _ => fun _ => 0) =
      ((a, g, c, sd), withSib u fun _ => fun _ => 0) := rfl
  rw [hyb3', hyb3', e1, e2, proveIdeal2_fillSib_zeroTail]

theorem hop2_tail :
    Close 0 (fun y : Hidden st.params × ((Bytes 16 × Grind) × Fallback st.params) =>
      hyb3' Hs T st r k y.2 (hiddenIdeal (ba (deltaOf y.2.1.2)) y.1))
      (fun y : Hidden st.params × ((Bytes 16 × Grind) × Fallback st.params) =>
        hyb3' Hs T st r k y.2 y.1) :=
  (close_self le_rfl _).congr (fun y => hyb3'_zeroTail Hs T st r k y.2 y.1) fun _ => rfl

/-- `tapeOfHidden` with a fallback block, as a bijection. -/
def tapeEquiv2 (p : Params) :
    (Hidden p × ((Bytes 16 × Grind) × Fallback p)) × Sib ≃ IdealTape2 p where
  toFun x := (tapeOfHidden x.1.2.1.1 x.1.2.1.2 x.1.1 x.2, x.1.2.2)
  invFun t := (((t.1.1.2.2.1, t.1.1.2.2.2, dropSib t.1.2), ((t.1.1.1, t.1.1.2.1), t.2)),
    t.1.2.2.2.2.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem hop2_tape :
    Close 0 (fun y : Hidden st.params × ((Bytes 16 × Grind) × Fallback st.params) =>
      hyb3' Hs T st r k y.2 y.1)
      (fun t : IdealTape2 st.params =>
        proveIdeal2 Hs T st r k (fillSib Hs T (st1 st) t.1, t.2)) := by
  have e1 : Close 0 (fun x : (Hidden st.params × ((Bytes 16 × Grind) × Fallback st.params)) × Sib =>
      hyb3' Hs T st r k x.1.2 x.1.1)
      (fun y : Hidden st.params × ((Bytes 16 × Grind) × Fallback st.params) =>
        hyb3' Hs T st r k y.2 y.1) := by
    -- (`convert`: elaborating against the expected type exhausts the recursion depth.)
    convert close_prod_fst (β := Sib)
      (X := fun y : Hidden st.params × ((Bytes 16 × Grind) × Fallback st.params) =>
        hyb3' Hs T st r k y.2 y.1)
  have e2 : Close 0 (fun x : (Hidden st.params × ((Bytes 16 × Grind) × Fallback st.params)) × Sib =>
      proveIdeal2 Hs T st r k (fillSib Hs T (st1 st) (tapeEquiv2 st.params x).1,
        (tapeEquiv2 st.params x).2))
      (fun t : IdealTape2 st.params => proveIdeal2 Hs T st r k (fillSib Hs T (st1 st) t.1, t.2)) :=
    close_equiv (tapeEquiv2 st.params)
      (fun t => proveIdeal2 Hs T st r k (fillSib Hs T (st1 st) t.1, t.2))
  have e3 : ∀ x : (Hidden st.params × ((Bytes 16 × Grind) × Fallback st.params)) × Sib,
      proveIdeal2 Hs T st r k (fillSib Hs T (st1 st) (tapeEquiv2 st.params x).1,
        (tapeEquiv2 st.params x).2) = hyb3' Hs T st r k x.1.2 x.1.1 :=
    fun x => by
      rw [hyb3', show (tapeEquiv2 st.params x).1 = tapeOfHidden x.1.2.1.1 x.1.2.1.2 x.1.1 x.2 from rfl,
        fillSib_tapeOfHidden Hs T (st1 st) _ _ _ x.2 fun _ => fun _ => 0]
      rfl
  exact ((e1.symm.trans (e2.congr e3 fun _ => rfl)).mono (by norm_num))

/-- **The two-phase tape hypothesis from one hypothesis per hop**, with
`ε = ε_rho + ε_grind + ε_abort + ε_bavc + ε_lab` (`ε_abort = noHitProb`). -/
theorem tapeHyp2_of_hops (hHs : HashesWF Hs) (hbavc : BAVCComplete)
    (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    {εrho εgrind εbavc εlab : ℝ} (h : HopHyps2 Hs T st r k εrho εgrind εbavc εlab) :
    TapeHyp2 Hs T st r k (εrho + εgrind + noHitProb + εbavc + εlab) := by
  have := ((((((hop2_h1 Hs T st r k hHs h.rho).trans (hop2_grind Hs T st r k h.grind)).trans
    (hop2_abort Hs T st r k)).trans (hop2_hide Hs T st r k hHs hbavc hlab h.bavc)).trans
    (hop2_tail Hs T st r k)).trans (hop2_tape Hs T st r k)).trans h.lab
  exact this.mono (by linarith)

end TwoPhase

end VoleMole.ZK.Sim
