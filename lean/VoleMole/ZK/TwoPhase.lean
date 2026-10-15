import VoleMole.ZK.Exec

/-!
# Zero knowledge of the two-phase prover (delayed instance; `lean/docs/zk.md` §7.5, §10.1)

PomFRIT's prover runs in two steps: step 1 (`Prover.voleGen`) commits with the witness prefix `r`
only, outputs the proof buffer written so far and `chal1`, and the environment then chooses the
instance (PomFRIT: `h = hash_to_target(…, chal1, …)`, the Signer's response) and the rest of the
witness; step 2 (`Prover.proveCommit`) finishes the proof. Here the zero-knowledge argument of
`ZK/Exec.lean` is extended to this flow, for any statement whose instance is bound after step 1
(`withInst st x`: `mu₁ = H₂⁴(DST ‖ 12)`, the instance in `chal2`) and any continuation `k` that maps
step 1's output to an instance and a witness suffix (or stops).

## What step 1 reveals

Step 1's output is `c₁ … c₁₆`, `c_mult`, the VOLE check `ũ`, `d[0..|r|)` and `iv_pre` (the other
fields are zero), and `chal1`, a hash of them. With dedicated label rows none of it depends on the
witness beyond `d[0..|r|) = u[0..|r|) ⊕ r`, a one-time pad: the corrections are padded by the
small VOLEs' inputs, `c_mult` by the sibling `H₅` answers, `ũ` by the four direct masks
(hybrids H5–H7 of the single-phase proof). So the simulator's step 1 outputs uniform fields and
the verifier's `chal1` (`simPhase1`); its step 2 uniform `d[|r|..)` and `ã`.

## Results

* `realRun2`, `proveIdeal2`, `simRun2`: the real two-phase run, the ideal-tape run, the simulated
  run (output: step 1's buffer, `chal1`, and step 2's proof if the environment continued). The
  ideal and simulated runs take `(ctr, Δ)` from their own grinding answers before step 1; if there
  is no accepted answer they output step 1 from a fallback block of the tape (`Fallback`) and fail
  in step 2. The real run's tape (`tapeOf2`) puts its own step-1 output there.
* **`realRun2_eq`** (no probability): the real run is the ideal-tape run at its own tape, from
  `proveCommit_eq_proveIdeal` (step 2) and `idealPhase1_real` (step 1).
* **`proveIdeal2_close`**: on a uniform tape the ideal run is distributed exactly as the simulated
  one, for every continuation. The proof is that of `proveIdeal_close`, with the instance, the
  witness suffix and hence `d[|r|..)` and `ã` chosen from step 1's output: `ã` is a bijection of the
  QuickSilver masks for every value of `ũ` and of the instance (`upush_respAd`, from `upush_resp`),
  and `(c_i, d)` a bijection of the row pads for every choice of the suffix that depends on
  `(c_i, d[0..|r|))` only (`rowsAdEquiv`).
* **`twoPhase_close`**: `Close ε` between the real and the simulated run, under the two-phase tape
  hypothesis `TapeHyp2` (hybrids H1, H4, H6 and the grinding answers, as `TapeHyp`) and the
  deterministic hypotheses `RunHyp2` (those of `ZKHyp` for every instance and suffix the
  continuation may pick, `BAVCComplete`, `CrtComplete`). **`twoPhase_close_tables`**: the same for
  faest-arch-opt's tables, where `RunHyp2.of_tables` proves the CRT certificate and both
  completeness facts.

`ZK/TwoPhaseHops.lean` derives `TapeHyp2` from one hypothesis per hop (`tapeHyp2_of_hops`).
`Privacy/PomFRITLean.lean` instantiates this for PomFRIT (`blindness_lean`).
-/

open Finset

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy

/-! ## Statements with the instance chosen after step 1 -/

/-- The part of a statement chosen after step 1: the instance encoding, the combination, the
constraints and the `chal2` binder (and, for the proofs, the system the constraints evaluate). -/
structure Inst2 where
  instEnc : ByteArray → ByteArray := fun _ => .empty
  comb : Option (ℕ × ByteArray) := none
  values : ByteArray → ByteArray → (ℕ → GF128) → List GF128 := fun _ _ _ => []
  binder2 : ByteArray := .empty
  /-- The constraint system `values` evaluates (`chal1 ↦ l ↦` a system), for the proofs. -/
  sys : ByteArray → ByteArray → System GF128 := fun _ _ => []

instance : Inhabited Inst2 := ⟨{}⟩

/-- `st` with delayed instance binding and the instance part `x`. Its parameters, DST and `chal1`
binder are `st`'s, and `mu₁ = H₂⁴(DST ‖ 12)` does not read the instance, so step 1 is the same
for every `x`. -/
@[reducible] def withInst (st : Statement) (x : Inst2) : Statement :=
  { st with
    delayed := true
    instEnc := x.instEnc
    comb := x.comb
    values := x.values
    binder2 := x.binder2 }

/-- The statement step 1 runs for (any `withInst st x` gives the same step 1). -/
abbrev st1 (st : Statement) : Statement := withInst st default

lemma mu1_withInst (Hs : Hashes) (st : Statement) (x : Inst2) :
    (withInst st x).mu1 Hs = mu Hs none st.dst := rfl

/-- The environment after step 1: from step 1's proof buffer and `chal1`, an instance and the
witness suffix, or `none` (no step 2). -/
abbrev Cont2 := ByteArray × ByteArray → Option (Inst2 × ByteArray)

/-- The output of a two-phase run: step 1's proof buffer, `chal1`, and step 2's proof if the
environment continued. -/
abbrev Out2 := ByteArray × ByteArray × Option (Except String ByteArray)

/-! ## The real run -/

/-- Step 1 with the witness prefix `r`. -/
def step1 (Hs : Hashes) (T : CrtTables) (st : Statement) (r rho : ByteArray) : Prover.Pending :=
  Prover.voleGen Hs T st.params (mu Hs none st.dst) r rho st.binder1

/-- **The real two-phase run**: step 1 with `r`, then step 2 for the instance and suffix the
continuation picks. -/
def realRun2 (Hs : Hashes) (T : CrtTables) (st : Statement) (r : ByteArray) (k : Cont2)
    (rho : ByteArray) : Out2 :=
  let s := step1 Hs T st r rho
  (s.proof, s.chal1,
    (k (s.proof, s.chal1)).map fun x => Prover.proveCommit Hs (withInst st x.1) x.2 s)

/-! ## The ideal run and the simulator -/

/-- The fallback block of a tape: step 1's output when there is no accepted grinding answer. -/
abbrev Fallback (p : Params) := Bytes p.proofBytes × Bytes 136

abbrev IdealTape2 (p : Params) := IdealTape p × Fallback p

abbrev SimCoins2 (p : Params) := SimCoins p × Fallback p

/-- **The ideal prover's step 1**, after the grinding outcome: the code of `idealCore` up to the
VOLE check, and `d` on the prefix `r`; the proof buffer and `chal1`. -/
def idealPhase1 (Hs : Hashes) (T : CrtTables) (st : Statement) (r : ByteArray) (s : Shared)
    (ctr : ℕ) (delta : Bytes 16) (t : Pads st.params) : ByteArray × ByteArray :=
  let p := st.params
  let P := pubOf Hs st s delta
  let us := usOf p t
  let u := us[0]!
  let corrections := correctionsOf p us
  let uMask := uMaskOfHi p T (ba t.2.2.2.2.2.1) us
  let cmult := cmultIdeal Hs T st P delta (qcolsOf st P delta corrections) u uMask t.2.2.2.2.2.2
  let ub := bytesOfWords u
  let dPre : ByteArray := ⟨(Array.range r.size).map fun j => ub.get! j ^^^ r.get! j⟩
  let ut := tUt Hs st s ctr delta corrections cmult ((Array.range p.correctionRows).map (wbit u))
    uMask
  (Prover.assemble p (tF1 s ctr delta corrections cmult ut dPre),
    tC1 Hs st s ctr delta corrections cmult)

/-- **The ideal-tape two-phase run**: the grinding outcome from the tape, step 1 (`idealPhase1`),
then `idealCore` for the instance and suffix the continuation picks. -/
def proveIdeal2 (Hs : Hashes) (T : CrtTables) (st : Statement) (r : ByteArray) (k : Cont2)
    (t : IdealTape2 st.params) : Out2 :=
  match firstHit t.1.1.2.1 with
  | none => (ba t.2.1, ba t.2.2, (k (ba t.2.1, ba t.2.2)).map fun _ => .error "grinding failed")
  | some (ctr, delta) =>
    let o := idealPhase1 Hs T (st1 st) r t.1.1 ctr delta t.1.2
    (o.1, o.2, (k o).map fun x => idealCore Hs T (withInst st x.1) (r ++ x.2) t.1.1 ctr delta t.1.2)

/-- Step 1's output from the fields `c_i`, `c_mult`, `ũ` and `d` (of which the first `n` bytes are
written): the proof buffer, and `chal1` as the verifier computes it. -/
def phase1Of (Hs : Hashes) (st : Statement) (n : ℕ) (s : Shared) (ctr : ℕ) (delta : Bytes 16)
    (c : Bytes (16 * st.params.correctionBytes))
    (cm : Bytes (st.params.nMask * st.params.nMultBytes)) (ut : Bytes 64)
    (d : Bytes st.params.witnessBytes) : ByteArray × ByteArray :=
  (Prover.assemble st.params { tF0 s ctr delta (ba c) (ba cm) with
      voleCheck := ba ut, correction := (ba d).extract 0 n },
    tC1 Hs st s ctr delta (ba c) (ba cm))

/-- **The simulated step 1**: the public part and the coins' `c_i`, `c_mult`, `ũ`, `d[0..n)`. -/
def simPhase1 (Hs : Hashes) (st : Statement) (n : ℕ) (s : Shared) (ctr : ℕ) (delta : Bytes 16)
    (f : SimFields st.params) : ByteArray × ByteArray :=
  phase1Of Hs st n s ctr delta f.1 f.2.1 f.2.2.1 f.2.2.2.1

/-- **The simulated two-phase run**: the witness and the instance are never read; step 2 outputs
the simulated proof (`Sim.simulate`'s). -/
def simRun2 (Hs : Hashes) (st : Statement) (n : ℕ) (k : Cont2) (c : SimCoins2 st.params) : Out2 :=
  match firstHit c.1.1.2.1 with
  | none => (ba c.2.1, ba c.2.2, (k (ba c.2.1, ba c.2.2)).map fun _ => .error "grinding failed")
  | some (ctr, delta) =>
    let o := simPhase1 Hs (st1 st) n c.1.1 ctr delta c.1.2
    (o.1, o.2, (k o).map fun _ => .ok (simAssemble st.params c.1.1 ctr delta c.1.2))

/-- The tape of a real two-phase run: `tapeAt` of step 1 with the grinding answers at the points of
the instance and suffix the continuation picks (any, if it stops), and step 1's output as the
fallback block. -/
def tapeOf2 (Hs : Hashes) (T : CrtTables) (st : Statement) (r : ByteArray) (k : Cont2)
    (rho : ByteArray) : IdealTape2 st.params :=
  let s := step1 Hs T st r rho
  let x := (k (s.proof, s.chal1)).getD (default, .empty)
  (tapeAt Hs T st.params s (realGrind Hs (realPre Hs (withInst st x.1) s (r ++ x.2))),
    (blk _ s.proof, blk 136 s.chal1))

/-- **The two-phase tape hypothesis**: the real run's tape, seen through the ideal-tape run, is
`ε`-close to uniform (as `TapeHyp`). -/
def TapeHyp2 (Hs : Hashes) (T : CrtTables) (st : Statement) (r : ByteArray) (k : Cont2)
    (ε : ℝ) : Prop :=
  Close ε (fun ρ : Bytes 16 => proveIdeal2 Hs T st r k (tapeOf2 Hs T st r k (ba ρ)))
    (proveIdeal2 Hs T st r k)

/-! ## The real run is the ideal run at its tape -/

/-- **Step 1 of the ideal run, at the real run's tape**, is the real step 1, at any accepted
grinding outcome. -/
theorem idealPhase1_real (Hs : Hashes) (T : CrtTables) (st : Statement) (r rho : ByteArray)
    (hHs : HashesWF Hs) (hbavc : BAVCComplete)
    (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    (g : Fin nGrind → Bytes 16) {ctr : ℕ} {d : Bytes 16} (hg : firstHit g = some (ctr, d)) :
    idealPhase1 Hs T (st1 st) r (tapeAt Hs T st.params (step1 Hs T st r rho) g).1 ctr d
        (tapeAt Hs T st.params (step1 Hs T st r rho) g).2 =
      ((step1 Hs T st r rho).proof, (step1 Hs T st r rho).chal1) := by
  set s := step1 Hs T st r rho with hsdef
  have hs : Prover.voleGen Hs T (st1 st).params ((st1 st).mu1 Hs) r rho (st1 st).binder1 = s := rfl
  have hcount : openCount (ba d) ≤ 105 := by
    have := firstHit_accepts hg
    simp only [accepts, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    exact this.2
  obtain ⟨opening, hopen⟩ := Option.isSome_iff_exists.1
    (by rw [openAt_isSome]; simpa using hcount : (BAVC.openAt s.tree s.leaves.coms (ba d)).isSome)
  show idealPhase1 Hs T (st1 st) r (tapeAt Hs T (st1 st).params s g).1 ctr d
    (tapeAt Hs T (st1 st).params s g).2 = _
  have ht : tapeAt Hs T (st1 st).params s g =
      ((blk 16 s.ivPre, g, comsOf s.leaves.coms (ba d), seedsOf s.tree (ba d)),
        realPads Hs T (st1 st).params s (ba d)) := by
    simp only [tapeAt, hg, Option.map_some, Option.getD_some]
  rw [ht]
  obtain ⟨hus, hu0, hcorr, huM, -, -, hqcols, hcmI, h1, h4⟩ :=
    step1_real Hs T (st1 st) s hs hHs hbavc hlab g ctr (size_ba d) hopen
  simp only [blk_ba] at hqcols hcmI h1 h4
  have spec := voleGen_spec Hs T (st1 st).params ((st1 st).mu1 Hs) r rho (st1 st).binder1
  have more := voleGen_more Hs T (st1 st).params ((st1 st).mu1 Hs) r rho (st1 st).binder1
  rw [hs] at spec more
  obtain ⟨-, -, -, hsivp, -, -, -, -, hsfiv, hsqs, -, -, -, -, -, hsvc, -⟩ := spec
  obtain ⟨-, -, -, hsop, hsdl, hsct, -⟩ := more
  have hivs : s.ivPre.size = 16 := by rw [hsivp, ByteArray.size_extract, hHs]; rfl
  unfold idealPhase1
  dsimp only
  rw [hus, hu0, hcorr, huM, hqcols, hcmI, h4, h1]
  have hF0 : tF0 (blk 16 s.ivPre, g, comsOf s.leaves.coms (ba d), seedsOf s.tree (ba d)) ctr d
      s.fields.corrections s.fields.cmult =
      { s.fields with voleCheck := .empty, correction := .empty } := by
    simp only [tF0, publicFields, ba_blk_of_size hivs, hsqs, hsop, hsdl, hsct, hsfiv]
  simp only [tF1, hF0, ← hsvc]
  rfl

/-- **The real two-phase run is the ideal-tape run at its own tape** (no probability), for
witnesses that satisfy every instance the continuation may pick. -/
theorem realRun2_eq (Hs : Hashes) (T : CrtTables) (st : Statement) (r : ByteArray) (k : Cont2)
    (rho : ByteArray)
    (hk : ∀ o x sfx, k o = some (x, sfx) → ZKHypQ (withInst st x) (r ++ sfx) x.sys)
    (hHs : HashesWF Hs) (hbavc : BAVCComplete)
    (hcrt : CrtComplete (Hs.hash .h5) T (step1 Hs T st r rho))
    (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows) :
    realRun2 Hs T st r k rho = proveIdeal2 Hs T st r k (tapeOf2 Hs T st r k rho) := by
  set s := step1 Hs T st r rho with hsdef
  have hps : s.proof.size = st.params.proofBytes := Pending_proof_size s
  have hcs : s.chal1.size = 136 := hHs .h21 _
  have hf1 : ba (blk st.params.proofBytes s.proof) = s.proof := ba_blk_of_size hps
  have hf2 : ba (blk 136 s.chal1) = s.chal1 := ba_blk_of_size hcs
  unfold realRun2 proveIdeal2 tapeOf2
  dsimp only
  rw [← hsdef]
  rcases hk' : k (s.proof, s.chal1) with _ | ⟨x, sfx⟩
  · simp only [Option.getD_none, Option.map_none]
    generalize realGrind Hs _ = g
    rcases hg : firstHit g with _ | ⟨ctr, d⟩
    · have : (tapeAt Hs T st.params s g).1.2.1 = g := rfl
      rw [this, hg]
      simp only [hf1, hf2, hk', Option.map_none]
    · have : (tapeAt Hs T st.params s g).1.2.1 = g := rfl
      rw [this, hg]
      dsimp only
      rw [idealPhase1_real Hs T st r rho hHs hbavc hlab g hg, ← hsdef, hk']
      rfl
  · have hz := hk _ _ _ hk'
    have e : Prover.proveCommit Hs (withInst st x) sfx s =
        proveIdeal Hs T (withInst st x) (r ++ sfx)
          (tapeAt Hs T st.params s
            (realGrind Hs (realPre Hs (withInst st x) s (r ++ sfx)))) :=
      proveCommit_eq_proveIdeal Hs T (withInst st x) r sfx rho x.sys hz hHs hbavc hcrt hlab
    simp only [Option.getD_some, Option.map_some, e]
    unfold proveIdeal
    have hw : ((r ++ sfx).size != (withInst st x).params.witnessBytes) = false := by
      simp [hz.hw]
    rw [hw]
    simp only [Bool.false_eq_true, ↓reduceIte]
    generalize realGrind Hs _ = g
    have : (tapeAt Hs T st.params s g).1.2.1 = g := rfl
    rw [this]
    rcases hg : firstHit g with _ | ⟨ctr, d⟩
    · simp only [hf1, hf2, hk', Option.map_some]
    · dsimp only
      rw [idealPhase1_real Hs T st r rho hHs hbavc hlab g hg, ← hsdef, hk']
      rfl

/-! ## On a uniform tape, the ideal run is the simulated run -/

section Bytes

variable {p : Params}

lemma extract_range_map (f : ℕ → UInt8) {m n : ℕ} (h : m ≤ n) :
    (⟨(Array.range n).map f⟩ : ByteArray).extract 0 m = ⟨(Array.range m).map f⟩ := by
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  apply Array.ext
  · simp; omega
  · intro i h1 h2
    simp

/-- `d` on the prefix `r`, from the pads. -/
lemma dPre_eq (t : Pads p) (r : ByteArray) (hr : r.size ≤ p.witnessBytes) :
    (⟨(Array.range r.size).map fun j => (bytesOfWords (usOf p t)[0]!).get! j ^^^ r.get! j⟩ :
      ByteArray) = (ba (dB r t)).extract 0 r.size := by
  rw [← correction_eq r t, extract_range_map _ hr]

lemma extract_ba_congr {n m : ℕ} {d d' : Bytes n} (hm : m ≤ n)
    (h : ∀ j : Fin n, j.val < m → d j = d' j) : (ba d).extract 0 m = (ba d').extract 0 m := by
  apply byteArray_ext_get!
  · simp
  intro j hj
  have hj' : j < m := by simp at hj; omega
  rw [get!_extract0 _ hj' (by simp [hm]), get!_extract0 _ hj' (by simp [hm]),
    get!_ba _ (by omega), get!_ba _ (by omega), h ⟨j, by omega⟩ hj']

lemma dB_append_pre (r x : ByteArray) (t : Pads p) (j : Fin p.witnessBytes) (hj : j.val < r.size) :
    dB (r ++ x) t j = dB r t j := by
  simp only [dB, get!_append, hj, ↓reduceIte]

/-- Re-pad `d` beyond the prefix `r`: `d ↦ d ⊕ (r ⊕ W(c, d))`. -/
def repad (r : ByteArray) (W : Bytes (16 * p.correctionBytes) → Bytes p.witnessBytes → ByteArray)
    (x : Bytes (16 * p.correctionBytes) × Bytes p.witnessBytes × Bytes (labelBytes p)) :
    Bytes (16 * p.correctionBytes) × Bytes p.witnessBytes × Bytes (labelBytes p) :=
  (x.1, fun j => x.2.1 j ^^^ (r.get! j ^^^ (W x.1 x.2.1).get! j), x.2.2)

/-- For a suffix choice `W` that reads `d` on the prefix only and agrees with `r` there, `repad`
is an involution. -/
lemma repad_repad (r : ByteArray)
    (W : Bytes (16 * p.correctionBytes) → Bytes p.witnessBytes → ByteArray)
    (hW : ∀ c d d', (∀ j : Fin p.witnessBytes, j.val < r.size → d j = d' j) → W c d = W c d')
    (hpre : ∀ c d (j : Fin p.witnessBytes), j.val < r.size → (W c d).get! j = r.get! j) (x) :
    repad r W (repad r W x) = x := by
  obtain ⟨c, d, θ⟩ := x
  have h1 : W c (fun j => d j ^^^ (r.get! j ^^^ (W c d).get! j)) = W c d :=
    hW _ _ _ fun j hj => by rw [hpre c d j hj, UInt8.xor_self, UInt8.xor_zero]
  simp only [repad, h1]
  refine Prod.ext rfl (Prod.ext (funext fun j => ?_) rfl)
  show d j ^^^ (r.get! j ^^^ (W c d).get! j) ^^^ (r.get! j ^^^ (W c d).get! j) = d j
  rw [UInt8.xor_assoc, UInt8.xor_self, UInt8.xor_zero]

/-- `repad` as a bijection. -/
def repadEquiv (r : ByteArray)
    (W : Bytes (16 * p.correctionBytes) → Bytes p.witnessBytes → ByteArray)
    (hW : ∀ c d d', (∀ j : Fin p.witnessBytes, j.val < r.size → d j = d' j) → W c d = W c d')
    (hpre : ∀ c d (j : Fin p.witnessBytes), j.val < r.size → (W c d).get! j = r.get! j) :
    (Bytes (16 * p.correctionBytes) × Bytes p.witnessBytes × Bytes (labelBytes p)) ≃
      (Bytes (16 * p.correctionBytes) × Bytes p.witnessBytes × Bytes (labelBytes p)) where
  toFun := repad r W
  invFun := repad r W
  left_inv := repad_repad r W hW hpre
  right_inv := repad_repad r W hW hpre

end Bytes

section Adaptive

variable (Hs : Hashes) (T : CrtTables) (st : Statement) (r : ByteArray) (k : Cont2)
  (s : Shared) (ctr : ℕ) (delta : Bytes 16)

lemma phase1Of_congr {n : ℕ} (hn : n ≤ st.params.witnessBytes)
    (c : Bytes (16 * st.params.correctionBytes))
    (cm : Bytes (st.params.nMask * st.params.nMultBytes)) (ut : Bytes 64)
    {d d' : Bytes st.params.witnessBytes}
    (h : ∀ j : Fin st.params.witnessBytes, j.val < n → d j = d' j) :
    phase1Of Hs st n s ctr delta c cm ut d = phase1Of Hs st n s ctr delta c cm ut d' := by
  unfold phase1Of
  rw [extract_ba_congr hn h]

/-- **Step 1 of the ideal run, from the pads**: `phase1Of` of `corrB`, `cmB`, the VOLE check `ũ`
and `dB`. -/
theorem idealPhase1_eq (hr : r.size ≤ st.params.witnessBytes) (t : Pads st.params) :
    idealPhase1 Hs T st r s ctr delta t = phase1Of Hs st r.size s ctr delta (corrB t)
      (cmB Hs T st s delta t)
      (gfsBytes 4 (utF Hs st s ctr delta (ba (corrB t)) (ba (cmB Hs T st s delta t))
        ((Array.range st.params.correctionRows).map (ubitF t)) (uOfM T (t.2.2.2.1, t.2.2.2.2.2.1))))
      (dB r t) := by
  unfold idealPhase1 phase1Of
  dsimp only
  rw [correctionsOf_eq, uMask_eq, uMaskArr_eq,
    Array.map_congr_left fun q hq => wbit_u_eq t (Array.mem_range.1 hq), dPre_eq t r hr]
  have hcm : cmultIdeal Hs T st (pubOf Hs st s delta) delta
      (qcolsOf st (pubOf Hs st s delta) delta (ba (corrB t))) (usOf st.params t)[0]!
      (arrU (uOfM T (t.2.2.2.1, t.2.2.2.2.2.1))) t.2.2.2.2.2.2 = ba (cmB Hs T st s delta t) := by
    rw [cmB, uMaskArr_eq, ba_blk_of_size (cmultIdeal_size _ _ _ _ _ _ _ _ _)]
  rw [hcm, tUt_eq]
  simp only [tF1, gfsToBytes_ofFn]

/-- The instance and suffix the continuation picks from step 1's fields (a default if it
stops). -/
def pick (c : Bytes (16 * st.params.correctionBytes))
    (cm : Bytes (st.params.nMask * st.params.nMultBytes)) (ut : Bytes 64)
    (d : Bytes st.params.witnessBytes) : Inst2 × ByteArray :=
  (k (phase1Of Hs (st1 st) r.size s ctr delta c cm ut d)).getD (default, .empty)

/-- `ũ` from the pads. -/
def utOf (t : Pads st.params) : Bytes 64 :=
  gfsBytes 4 (utF Hs (st1 st) s ctr delta (ba (corrB t)) (ba (cmB Hs T (st1 st) s delta t))
    ((Array.range st.params.correctionRows).map (ubitF t)) (uOfM T (t.2.2.2.1, t.2.2.2.2.2.1)))

/-- **The ideal run's fields, with the instance and suffix picked from step 1's** (`fieldsOf` at
them). -/
noncomputable def fieldsAd (t : Pads st.params) : SimFields st.params :=
  let x := pick Hs st r k s ctr delta (corrB t) (cmB Hs T (st1 st) s delta t)
    (utOf Hs T st s ctr delta t) (dB r t)
  (fieldsOf Hs T (withInst st x.1) (r ++ x.2) x.1.sys s ctr delta t).1

/-- The response fields `(ũ, ã)`, with the instance and suffix picked from `ũ` by `X`. -/
noncomputable def respAd (X : Bytes 64 → Inst2 × ByteArray) (dOf : ByteArray → ByteArray)
    (c cmult : ByteArray) (ubits : Array Bool) (U : Fin st.params.nMask → GF128) :
    Bytes 64 × Bytes (16 * (st.params.qsDegree - 1)) :=
  let ut := gfsBytes 4 (utF Hs (st1 st) s ctr delta c cmult ubits U)
  (ut, (respB Hs T (withInst st (X ut).1) (r ++ (X ut).2) s ctr delta (X ut).1.sys c cmult ubits
    (dOf (r ++ (X ut).2)) U).2)

/-- **H7 with the instance chosen after `ũ`**: uniform `u_mask` gives uniform `(ũ, ã)`, whatever
instance and suffix are picked from `ũ` (`upush_resp` allows the unmasked QuickSilver coefficients
to depend on `ũ`). -/
theorem upush_respAd (X : Bytes 64 → Inst2 × ByteArray) (dOf : ByteArray → ByteArray)
    (c cmult : ByteArray) (ubits : Array Bool) :
    UPush (respAd Hs T st r s ctr delta X dOf c cmult ubits) := by
  let H : (Fin 4 → GF128) → Fin (st.params.qsDegree - 1) → GF128 := fun y =>
    qsH Hs T (withInst st (X (gfsBytes 4 y)).1) (r ++ (X (gfsBytes 4 y)).2) s ctr delta
      (X (gfsBytes 4 y)).1.sys c cmult ubits (dOf (r ++ (X (gfsBytes 4 y)).2)) y
  have key : ∀ x, respAd Hs T st r s ctr delta X dOf c cmult ubits (splitE st.params x) =
      (gfsBytes 4 (x.2 + kosG Hs (st1 st) s ctr delta c cmult ubits x.1),
       gfsBytes (st.params.qsDegree - 1) (qsResponse
         (H (x.2 + kosG Hs (st1 st) s ctr delta c cmult ubits x.1))
         (qbar Hs T (st1 st) s delta c cmult) (tDL T delta) x.1)) := by
    intro x
    have hs : utF Hs (st1 st) s ctr delta c cmult ubits (splitE st.params x) =
        x.2 + kosG Hs (st1 st) s ctr delta c cmult ubits x.1 :=
      utF_split Hs (st1 st) s ctr delta c cmult ubits x
    unfold respAd respB
    dsimp only
    rw [hs]
    refine Prod.ext rfl (congrArg (gfsBytes _) (funext fun j => ?_))
    have e := tAt_get Hs T
      (withInst st (X (gfsBytes 4 (x.2 + kosG Hs (st1 st) s ctr delta c cmult ubits x.1))).1)
      (r ++ (X (gfsBytes 4 (x.2 + kosG Hs (st1 st) s ctr delta c cmult ubits x.1))).2) s ctr delta
      (X (gfsBytes 4 (x.2 + kosG Hs (st1 st) s ctr delta c cmult ubits x.1))).1.sys c cmult ubits
      (dOf (r ++ (X (gfsBytes 4 (x.2 + kosG Hs (st1 st) s ctr delta c cmult ubits x.1))).2)) x j
    rw [show utF Hs (withInst st (X (gfsBytes 4
      (x.2 + kosG Hs (st1 st) s ctr delta c cmult ubits x.1))).1) s ctr delta c cmult ubits
      (splitE (withInst st (X (gfsBytes 4
        (x.2 + kosG Hs (st1 st) s ctr delta c cmult ubits x.1))).1).params x) = _ from hs] at e
    exact e
  have h1 := upush_resp (kosG Hs (st1 st) s ctr delta c cmult ubits) H
    (qbar Hs T (st1 st) s delta c cmult) (tDL T delta)
  let E : (Fin (st.params.qsDegree - 1) → GF128) × (Fin 4 → GF128) ≃
      Bytes (16 * 4) × Bytes (16 * (st.params.qsDegree - 1)) :=
    (Equiv.prodComm _ _).trans
      (Equiv.prodCongr (gfsBytesEquiv 4) (gfsBytesEquiv (st.params.qsDegree - 1)))
  have h2 : UPush (fun y : (Fin (st.params.qsDegree - 1) → GF128) × (Fin 4 → GF128) =>
      (gfsBytes 4 y.2, gfsBytes (st.params.qsDegree - 1) y.1)) :=
    (upush_equiv E).congr fun y => by
      simp only [E, Equiv.trans_apply, Equiv.prodComm_apply, Equiv.prodCongr_apply, Prod.map,
        gfsBytesEquiv, Equiv.ofBijective_apply, Prod.fst_swap, Prod.snd_swap]
  have h3 := (upush_equiv (splitE st.params).symm).comp (h1.comp h2)
  refine h3.congr fun U => ?_
  have := key ((splitE st.params).symm U)
  rw [Equiv.apply_symm_apply] at this
  rw [this]
  rfl

/-- The inner fields for row pads `a`: `c_mult`, then `(ũ, ã)` for the instance and suffix
picked. -/
noncomputable def innerAd (a : RowPads st.params)
    (mc : MaskPads st.params × (Fin 312 → Bytes 4)) :
    Bytes (st.params.nMask * st.params.nMultBytes) ×
      (Bytes 64 × Bytes (16 * (st.params.qsDegree - 1))) :=
  (cmB Hs T (st1 st) s delta (padsOf a mc.1 mc.2),
    respAd Hs T st r s ctr delta
      (fun ut => pick Hs st r k s ctr delta (corrB (padsOf a (m0 _) c0))
        (cmB Hs T (st1 st) s delta (padsOf a mc.1 mc.2)) ut (dB r (padsOf a (m0 _) c0)))
      (fun w => ba (dB w (padsOf a (m0 _) c0))) (ba (corrB (padsOf a (m0 _) c0)))
      (ba (cmB Hs T (st1 st) s delta (padsOf a mc.1 mc.2)))
      ((Array.range st.params.correctionRows).map (ubitF (padsOf a (m0 _) c0))) (uOfM T mc.1))

/-- **For fixed row pads, `(c_mult, ũ, ã)` is uniform**, with the instance picked after step 1
(H6, §7.4, H7). -/
theorem upush_innerAd (hT : maskInvOk T = true) (hnm : st.params.nMask ≤ 32)
    (a : RowPads st.params) : UPush (innerAd Hs T st r k s ctr delta a) := by
  have h1 := upush_shear (α := MaskPads st.params) fun m =>
    upush_cmult Hs T (st1 st) (pubOf Hs (st1 st) s delta) delta
      (qcolsOf (st1 st) (pubOf Hs (st1 st) s delta) delta (ba (corrB (padsOf a m c0))))
      (usOf st.params (padsOf a m c0))[0]! (uMaskArr T (padsOf a m c0)) hnm
  have h2 := UPush.prodMap (upush_uOfM hT st.params)
    (upush_id (α := Bytes (st.params.nMask * st.params.nMultBytes)))
  have h3 := (upush_shear' (α := Fin st.params.nMask → GF128)
    fun cm : Bytes (st.params.nMask * st.params.nMultBytes) =>
    upush_respAd Hs T st r s ctr delta
      (fun ut => pick Hs st r k s ctr delta (corrB (padsOf a (m0 _) c0)) cm ut
        (dB r (padsOf a (m0 _) c0)))
      (fun w => ba (dB w (padsOf a (m0 _) c0))) (ba (corrB (padsOf a (m0 _) c0))) (ba cm)
      ((Array.range st.params.correctionRows).map (ubitF (padsOf a (m0 _) c0)))).comp
    (upush_equiv (Equiv.prodComm _ _))
  refine ((h1.comp h2).comp h3).congr fun mc => ?_
  simp only [innerAd]
  rw [cmB_padsOf Hs T (st1 st) s delta a mc.1 mc.2]
  rfl

/-- The row fields: `c_i`, `d` for the suffix picked from `(c_i, d[0..|r|))` and the inner fields
`y`, and `Θ`. -/
def rowsAd (y : Bytes (st.params.nMask * st.params.nMultBytes) ×
      (Bytes 64 × Bytes (16 * (st.params.qsDegree - 1))))
    (a : RowPads st.params) :
    Bytes (16 * st.params.correctionBytes) × Bytes st.params.witnessBytes ×
      Bytes (labelBytes st.params) :=
  (corrB (padsOf a (m0 _) c0),
    dB (r ++ (pick Hs st r k s ctr delta (corrB (padsOf a (m0 _) c0)) y.1 y.2.1
      (dB r (padsOf a (m0 _) c0))).2) (padsOf a (m0 _) c0), a.2.1)

/-- **H5 with the suffix chosen after step 1**: the row pads give uniform `(c_i, d, Θ)`, for every
value of the inner fields. -/
theorem upush_rowsAd (hn : r.size ≤ st.params.witnessBytes)
    (y : Bytes (st.params.nMask * st.params.nMultBytes) ×
      (Bytes 64 × Bytes (16 * (st.params.qsDegree - 1)))) :
    UPush (rowsAd Hs st r k s ctr delta y) := by
  let W : Bytes (16 * st.params.correctionBytes) → Bytes st.params.witnessBytes → ByteArray :=
    fun c d => r ++ (pick Hs st r k s ctr delta c y.1 y.2.1 d).2
  have hW : ∀ c d d', (∀ j : Fin st.params.witnessBytes, j.val < r.size → d j = d' j) →
      W c d = W c d' := fun c d d' h => by
    simp only [W, pick, phase1Of_congr Hs (st1 st) s ctr delta hn c y.1 y.2.1 h]
  have hpre : ∀ c d (j : Fin st.params.witnessBytes), j.val < r.size → (W c d).get! j = r.get! j :=
    fun c d j hj => by simp only [W, get!_append, hj, ↓reduceIte]
  have h1 : UPush (fun a : RowPads st.params => (a.1, a.2.1, a.2.2.1)) := by
    let e : RowPads st.params ≃ (Bytes st.params.witnessBytes × Bytes (labelBytes st.params) ×
        (Fin (BAVC.tau - 1) → Bytes st.params.correctionBytes)) ×
        (Fin BAVC.tau → Bytes (restBytes st.params)) :=
      { toFun := fun a => ((a.1, a.2.1, a.2.2.1), a.2.2.2)
        invFun := fun x => (x.1.1, x.1.2.1, x.1.2.2, x.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact ((upush_equiv e).comp upush_fst).congr fun _ => rfl
  refine ((h1.comp (upush_equiv (rowsEquiv st.params r))).comp
    (upush_equiv (repadEquiv r W hW hpre))).congr fun a => ?_
  refine Prod.ext rfl (Prod.ext (funext fun j => ?_) rfl)
  show dB (W (corrB (padsOf a (m0 _) c0)) (dB r (padsOf a (m0 _) c0))) (padsOf a (m0 _) c0) j =
    dB r (padsOf a (m0 _) c0) j ^^^ (r.get! j ^^^
      (W (corrB (padsOf a (m0 _) c0)) (dB r (padsOf a (m0 _) c0))).get! j)
  simp only [dB]
  rw [UInt8.xor_assoc, ← UInt8.xor_assoc (r.get! j), UInt8.xor_self, UInt8.zero_xor]

/-- **The ideal run's adaptive fields are uniform.** -/
theorem upush_fieldsAd (hT : maskInvOk T = true) (hnm : st.params.nMask ≤ 32)
    (hn : r.size ≤ st.params.witnessBytes) : UPush (fieldsAd Hs T st r k s ctr delta) := by
  have h1 := upush_shear (α := RowPads st.params) fun a =>
    upush_innerAd Hs T st r k s ctr delta hT hnm a
  have h2 := upush_shear' (β := Bytes (st.params.nMask * st.params.nMultBytes) ×
    (Bytes 64 × Bytes (16 * (st.params.qsDegree - 1)))) fun y =>
    upush_rowsAd Hs st r k s ctr delta hn y
  let R : (Bytes (16 * st.params.correctionBytes) × Bytes st.params.witnessBytes ×
      Bytes (labelBytes st.params)) × (Bytes (st.params.nMask * st.params.nMultBytes) ×
      (Bytes 64 × Bytes (16 * (st.params.qsDegree - 1)))) ≃
      SimFields st.params × Bytes (labelBytes st.params) :=
    { toFun := fun x => ((x.1.1, x.2.1, x.2.2.1, x.1.2.1, x.2.2.2), x.1.2.2)
      invFun := fun y => ((y.1.1, y.1.2.2.2.1, y.2), (y.1.2.1, y.1.2.2.1, y.1.2.2.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h3 := (upush_equiv (padsE st.params)).comp
    ((h1.comp h2).comp ((upush_equiv R).comp upush_fst))
  exact h3.congr fun _ => rfl

end Adaptive

/-! ## Zero knowledge -/

lemma map_congr_of {α β : Type*} {o : Option α} {f g : α → β} (h : ∀ a, o = some a → f a = g a) :
    o.map f = o.map g := by
  cases o with
  | none => rfl
  | some a => exact congrArg some (h a rfl)

section Close

variable (Hs : Hashes) (T : CrtTables) (st : Statement) (r : ByteArray) (k : Cont2)

/-- **On a uniform tape, the ideal two-phase run is distributed exactly as the simulated one**
(hybrids H2, H5–H7 with the instance chosen after step 1), for every continuation whose instances
and suffixes the witness satisfies. -/
theorem proveIdeal2_close
    (hk : ∀ o x sfx, k o = some (x, sfx) → ZKHypQ (withInst st x) (r ++ sfx) x.sys)
    (hr : r.size ≤ st.params.witnessBytes) (hnm : st.params.nMask ≤ 32)
    (hT : maskInvOk T = true) :
    Close 0 (proveIdeal2 Hs T st r k) (simRun2 Hs st r.size k) := by
  suffices hs : ∀ fb s, Close 0 (fun t : Pads st.params => proveIdeal2 Hs T st r k ((s, t), fb))
      (fun f : SimFields st.params => simRun2 Hs st r.size k ((s, f), fb)) by
    -- Average over the fallback block, then over the shared part (`convert`: the products'
    -- `Fintype` instances are found along different paths).
    have h1 : ∀ fb, Close 0 (fun t : IdealTape st.params => proveIdeal2 Hs T st r k (t, fb))
        (fun c : SimCoins st.params => simRun2 Hs st r.size k (c, fb)) := fun fb => by
      convert Close.prod_right
        (X := fun s (t : Pads st.params) => proveIdeal2 Hs T st r k ((s, t), fb))
        (Y := fun s (f : SimFields st.params) => simRun2 Hs st r.size k ((s, f), fb)) (hs fb)
    convert Close.prod_left
      (X := fun (t : IdealTape st.params) fb => proveIdeal2 Hs T st r k (t, fb))
      (Y := fun (c : SimCoins st.params) fb => simRun2 Hs st r.size k (c, fb)) h1
  intro fb s
  rcases hf : firstHit s.2.1 with _ | ⟨ctr, delta⟩
  · -- No accepted grinding answer: step 1 from the fallback block, step 2 fails.
    have e1 : ∀ t : Pads st.params, proveIdeal2 Hs T st r k ((s, t), fb) =
        (ba fb.1, ba fb.2, (k (ba fb.1, ba fb.2)).map fun _ => .error "grinding failed") :=
      fun t => by simp only [proveIdeal2, hf]
    have e2 : ∀ f : SimFields st.params, simRun2 Hs st r.size k ((s, f), fb) =
        (ba fb.1, ba fb.2, (k (ba fb.1, ba fb.2)).map fun _ => .error "grinding failed") :=
      fun f => by simp only [simRun2, hf]
    exact (close_const le_rfl _).congr e1 e2
  · -- The grinding outcome `(ctr, Δ)`; then the adaptive fields.
    let Φ : SimFields st.params → Out2 := fun f =>
      ((simPhase1 Hs (st1 st) r.size s ctr delta f).1,
        (simPhase1 Hs (st1 st) r.size s ctr delta f).2,
        (k (simPhase1 Hs (st1 st) r.size s ctr delta f)).map fun _ =>
          .ok (simAssemble st.params s ctr delta f))
    have e1 : ∀ t : Pads st.params, proveIdeal2 Hs T st r k ((s, t), fb) =
        Φ (fieldsAd Hs T st r k s ctr delta t) := by
      intro t
      have hp1 := idealPhase1_eq Hs T (st1 st) r s ctr delta hr t
      have hp2 : simPhase1 Hs (st1 st) r.size s ctr delta (fieldsAd Hs T st r k s ctr delta t) =
          idealPhase1 Hs T (st1 st) r s ctr delta t :=
        (phase1Of_congr Hs (st1 st) s ctr delta hr _ _ _ fun j hj => dB_append_pre r _ t j hj).trans
          hp1.symm
      simp only [proveIdeal2, hf, Φ]
      rw [hp2]
      refine Prod.ext rfl (Prod.ext rfl (map_congr_of fun x hko => ?_))
      obtain ⟨x, sfx⟩ := x
      have hz := hk _ _ _ hko
      have hpick : pick Hs st r k s ctr delta (corrB t) (cmB Hs T (st1 st) s delta t)
          (utOf Hs T st s ctr delta t) (dB r t) = (x, sfx) := by
        have e := congrArg (fun o => (k o).getD ((default : Inst2), ByteArray.empty)) hp1
        simp only [hko] at e
        exact e.symm
      refine (idealCore_fields Hs T (withInst st x) (r ++ sfx) x.sys hz.hvals hz.hdeg hz.hd hz.hd'
        hz.hI hz.hsat s ctr delta t).trans ?_
      have hfa : fieldsAd Hs T st r k s ctr delta t =
          (fieldsOf Hs T (withInst st x) (r ++ sfx) x.sys s ctr delta t).1 := by
        simp only [fieldsAd]
        rw [hpick]
      rw [hfa]
    have e2 : ∀ f : SimFields st.params, simRun2 Hs st r.size k ((s, f), fb) = Φ f := fun f => by
      simp only [simRun2, hf, Φ]
    exact ((upush_fieldsAd Hs T st r k s ctr delta hT hnm hr).close Φ).congr e1 e2

end Close

/-- The deterministic hypotheses of the two-phase theorem: those of `ZKHyp` for every instance and
suffix the continuation may pick (so that `Prover.qsProve` succeeds for the full witness
`r ++ suffix`), and those of `RunHyp` for step 1. -/
structure RunHyp2 (Hs : Hashes) (T : CrtTables) (st : Statement) (r : ByteArray) (k : Cont2) :
    Prop where
  hk : ∀ o x sfx, k o = some (x, sfx) → ZKHypQ (withInst st x) (r ++ sfx) x.sys
  hr : r.size ≤ st.params.witnessBytes
  hnm : st.params.nMask ≤ 32
  hT : maskInvOk T = true
  hHs : HashesWF Hs
  hbavc : BAVCComplete
  hcrt : ∀ rho : ByteArray, CrtComplete (Hs.hash .h5) T (step1 Hs T st r rho)
  hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows

/-- **The two-phase reduction**: the zero-knowledge advantage of any distinguisher equals its tape
advantage (no probabilistic hypothesis). -/
theorem twoPhase_reduction {Hs : Hashes} {T : CrtTables} {st : Statement} {r : ByteArray}
    {k : Cont2} (h : RunHyp2 Hs T st r k) (D : Out2 → Prop) :
    |pr (Bytes 16) (fun ρ => D (realRun2 Hs T st r k (ba ρ))) -
        pr (SimCoins2 st.params) (fun c => D (simRun2 Hs st r.size k c))| =
      |pr (Bytes 16) (fun ρ => D (proveIdeal2 Hs T st r k (tapeOf2 Hs T st r k (ba ρ)))) -
        pr (IdealTape2 st.params) (fun t => D (proveIdeal2 Hs T st r k t))| := by
  have h1 : ∀ ρ : Bytes 16, realRun2 Hs T st r k (ba ρ) =
      proveIdeal2 Hs T st r k (tapeOf2 Hs T st r k (ba ρ)) := fun ρ =>
    realRun2_eq Hs T st r k (ba ρ) h.hk h.hHs h.hbavc (h.hcrt _) h.hlab
  have h2 := proveIdeal2_close Hs T st r k h.hk h.hr h.hnm h.hT D
  rw [abs_nonpos_iff, sub_eq_zero] at h2
  simp only [h1, h2]

/-- **Zero knowledge of the two-phase prover from the tape hypothesis**: the real run (uniform
`rho`) and the simulated run are `ε`-close, for every distinguisher. -/
theorem twoPhase_close {Hs : Hashes} {T : CrtTables} {st : Statement} {r : ByteArray} {k : Cont2}
    (h : RunHyp2 Hs T st r k) {ε : ℝ} (ht : TapeHyp2 Hs T st r k ε) :
    Close ε (fun ρ : Bytes 16 => realRun2 Hs T st r k (ba ρ)) (simRun2 Hs st r.size k) := by
  intro D
  rw [twoPhase_reduction h D]
  exact ht D

/-- `RunHyp2` for faest-arch-opt's tables: the CRT certificate (`maskInvOk_tables`), BAVC and CRT
completeness (`Bridge.bavcComplete`, `Bridge.crtComplete`) are theorems. -/
theorem RunHyp2.of_tables {Hs : Hashes} {st : Statement} {r : ByteArray} {k : Cont2}
    (hk : ∀ o x sfx, k o = some (x, sfx) → ZKHypQ (withInst st x) (r ++ sfx) x.sys)
    (hr : r.size ≤ st.params.witnessBytes) (hnm : st.params.nMask ≤ 32) (hHs : HashesWF Hs)
    (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows) :
    RunHyp2 Hs CrtGen.tables st r k :=
  ⟨hk, hr, hnm, maskInvOk_tables, hHs, bavcComplete,
    fun rho => crtComplete Hs st.params _ r rho _ hlab, hlab⟩

/-- **Two-phase zero knowledge with faest-arch-opt's tables**, from the tape hypothesis and the
hypotheses of `ZKHyp` for every instance the continuation picks. -/
theorem twoPhase_close_tables {Hs : Hashes} {st : Statement} {r : ByteArray} {k : Cont2}
    (hk : ∀ o x sfx, k o = some (x, sfx) → ZKHypQ (withInst st x) (r ++ sfx) x.sys)
    (hr : r.size ≤ st.params.witnessBytes) (hnm : st.params.nMask ≤ 32) (hHs : HashesWF Hs)
    (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows) {ε : ℝ}
    (ht : TapeHyp2 Hs CrtGen.tables st r k ε) :
    Close ε (fun ρ : Bytes 16 => realRun2 Hs CrtGen.tables st r k (ba ρ))
      (simRun2 Hs st r.size k) :=
  twoPhase_close (RunHyp2.of_tables hk hr hnm hHs hlab) ht

end VoleMole.ZK.Sim
