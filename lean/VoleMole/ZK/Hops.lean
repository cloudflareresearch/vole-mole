import VoleMole.ZK.TapeOf
import VoleMole.Privacy.Hybrid

/-!
# The tape hypothesis from one assumption per hop (`lean/docs/zk.md` H1, H2, H4, H6)

`ZK/Exec.lean` reduces zero knowledge of the executable prover to the tape hypothesis
`TapeHyp … ε`: the real run's tape `tapeOf … rho` is `ε`-close to a uniform ideal tape, seen
through the ideal-tape prover. Here that tape is taken apart, and the hypothesis is proved from one
assumption per hop, each a `Close` bound on a small explicit experiment, by the hybrid argument
(`Close.trans`, `Close.map`, averaging over the coordinates the hop does not touch):

* **H1** (`H3Hyp`, `ε_rho`): `H₃`'s answer at the seed input `w_pre ‖ mu ‖ rho ‖ 3` (the root seed
  and `iv_pre`, `h3Seed`) is close to uniform, for uniform `rho`. In the ROM it holds with `ε = 0`,
  and `≤ q₃·2⁻¹²⁸` against a distinguisher that reads `H₃` at `q₃` inputs (`h3_rom`,
  `h3_rom_query`, `ZK/HopsROM.lean`).
* **Grinding** (`GrindHyp`, `ε_grind`; H2's freshness): the `H₂³` answers at the run's `2³²`
  grinding points (`realGrind`, at a prefix that is a function of the seed and `iv_pre`) are close
  to uniform and independent of them. In the ROM it holds with `ε = 0`, and programming the oracle
  at the grinding points, as the simulator does, is perfect (`grind_rom`, `grind_rom_program`); the
  prover's prefix does not read `H₂³` (`realPre_pendAt_congr`, `grind_rom_prover`).
* **H4** (`HideHyp`, `ε_bavc`: BAVC hiding, `ε_hide` of zk.md §3): for any `iv` and `Δ`, the hidden
  part of a commitment from a uniform root seed (`hiddenOut`: the hidden leaves' commitments, the
  opened seeds, the small VOLEs' inputs `u^{(i)}` on all rows and the root PRG's `u_hi`) is close
  to uniform (`hiddenIdeal`: the seed slots past the `openCount Δ` opened ones are zero, as in the
  real opening). It depends only on AES and the parameters (no hash): PRG/GGM security with AES as
  an ideal cipher or PRP, the inputs of the four roles being distinct
  (`Bridge.ctrBlock_ne_of_roles`). An assumption.
* **H6** (`LabHyp`, `ε_lab`): on a uniform tape, filling in the `H₅` answers at the sibling labels
  the tape determines (`fillSib`) is close to leaving them uniform, through the ideal-tape prover.
  In the ROM the gap is the probability that a sibling input is read (`lab_rom`), at most
  `(q₅ + 1)·2⁻¹²⁸` against a distinguisher that reads `H₅` at `q₅` inputs (`lab_rom_hyp`,
  `ZK/HopsH6.lean`).

**`tape_close_of_hops`**: from the four hypotheses (`HopHyps`; and the deterministic `HashesWF`,
`BAVCComplete`, label rows), the tape hypothesis holds with `ε_rho + ε_grind + ε_bavc + ε_lab`
(`ZK/Exec.lean`: `tapeHyp_of_hops`).

The hybrids, through the ideal-tape prover `V = proveIdeal Hs T st w`:
1. `rho` ↦ `V (tapeOf … rho)`: the real run (`tapeOf_eq_tape1`);
2. `(seed, iv_pre)` uniform ↦ `V (tapeAt (pendAt …) (realGrind …))` (H1);
3. `(seed, iv_pre, g)` uniform ↦ `V (tapeAt (pendAt …) g)` (grinding);
4. the sibling answers recomputed from the tape (`real_fillSib`: the real run's are those), and
   `(hidden part, iv_pre, g)` uniform (H4); the seed slots past the opened ones do not matter
   (`proveIdeal_fillSib_zeroTail`);
5. the uniform ideal tape (H6).

The hybrid composition is exact apart from the four terms: no other step loses anything.
-/

open Finset

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy

lemma firstHit_accepts {g : Fin nGrind → Bytes 16} {ctr : ℕ} {d : Bytes 16}
    (h : firstHit g = some (ctr, d)) : accepts (ba d) = true := by
  obtain ⟨c, hc⟩ := findFirst_some _ _ _ h
  split_ifs at hc with h1 h2
  simp only [Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  exact h2

lemma blk_ba {n : ℕ} (d : Bytes n) : blk n (ba d) = d := by
  funext i; rw [get_blk, get!_ba _ i.isLt]

/-! ## The pieces of a tape -/

/-- The grinding answers of a tape. -/
abbrev Grind := Fin nGrind → Bytes 16

/-- The tape's `Δ`: the first accepted grinding answer (zero if there is none), as in `tapeAt`. -/
def deltaOf (g : Grind) : Bytes 16 := ((firstHit g).map (·.2)).getD fun _ => 0

/-- The pads without the sibling answers: the small VOLEs' inputs and `u_hi`. -/
abbrev PadsU (p : Params) :=
  Bytes p.witnessBytes × Bytes (labelBytes p) × (Fin (BAVC.tau - 1) → Bytes p.correctionBytes) ×
    (Fin BAVC.tau → Bytes p.nMask) × (Fin BAVC.tau → Bytes (restBytes p)) × Bytes p.nMask

/-- The sibling answers' block of the pads. -/
abbrev Sib := Fin 312 → Bytes 4

def dropSib {p : Params} (t : Pads p) : PadsU p :=
  (t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1)

def withSib {p : Params} (u : PadsU p) (z : Sib) : Pads p :=
  (u.1, u.2.1, u.2.2.1, u.2.2.2.1, u.2.2.2.2.1, u.2.2.2.2.2, z)

/-- **The hidden part of a commitment** (hybrid H4): the hidden leaves' commitments, the opened
seeds and the pads without the sibling answers. -/
abbrev Hidden (p : Params) := (Fin BAVC.tau → Bytes 32) × (Fin 105 → Bytes 16) × PadsU p

/-- **The hidden part of the commitment from the root seed `seed`** at `iv` and `Δ`: `BAVC.commit`,
the small VOLEs' inputs of all leaves (`realUs`) and the root PRG's `u_hi`. -/
def hiddenOut (p : Params) (iv delta : ByteArray) (seed : Bytes 16) : Hidden p :=
  let tl := BAVC.commit (ba seed) iv
  let us : Array ByteArray := (Array.range BAVC.tau).map fun i =>
    bytesOfWords (Prover.smallVoleUWords p iv i (leafKey tl.2 i))
  (comsOf tl.2.coms delta, seedsOf tl.1 delta, dropSib (padsOfArrays p us
    (AES.prg (ba seed) iv (((1 : UInt32) <<< 31) - 1) 0 ((8 * p.nMask + 127) / 128)) #[]))

/-- The seed slots past the `openCount Δ` opened seeds, zeroed (as `seedsOf` leaves them). -/
def zeroTail (delta : ByteArray) (sd : Fin 105 → Bytes 16) : Fin 105 → Bytes 16 :=
  fun k => if k.val < openCount delta then sd k else fun _ => 0

/-- The ideal hidden part: uniform, with the unused seed slots zero. -/
def hiddenIdeal {p : Params} (delta : ByteArray) (h : Hidden p) : Hidden p :=
  (h.1, zeroTail delta h.2.1, h.2.2)

/-- The tape from the hidden part, `iv_pre`, the grinding answers and the sibling answers. -/
def tapeOfHidden {p : Params} (ivPre : Bytes 16) (g : Grind) (h : Hidden p) (z : Sib) :
    IdealTape p :=
  ((ivPre, g, h.1, h.2.1), withSib h.2.2 z)

/-- `tapeOfHidden` as a bijection. -/
def tapeEquiv (p : Params) : (Hidden p × (Bytes 16 × Grind)) × Sib ≃ IdealTape p where
  toFun x := tapeOfHidden x.1.2.1 x.1.2.2 x.1.1 x.2
  invFun t := (((t.1.2.2.1, t.1.2.2.2, dropSib t.2), (t.1.1, t.1.2.1)), t.2.2.2.2.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-! ## The sibling answers a tape determines -/

/-- **The `H₅` answers at the sibling labels of a tape** (`L^{1−γ_e}_e`), from its shared part and
its pads (not their sibling answers): the labels of the prover's tags `q + Δ·u` (`tagCols`), as in
`cmultIdeal`. At the real run's tape these are the run's own sibling answers (`real_fillSib`). -/
def sibOf (Hs : Hashes) (T : CrtTables) (st : Statement) (s : Shared) (t : Pads st.params) : Sib :=
  let p := st.params
  let delta := deltaOf s.2.1
  let P := pubOf Hs st s delta
  let us := usOf p t
  let uu := us[0]!
  let dbit := BAVC.deltaBit (ba delta)
  let cols := tagCols dbit (qcolsOf st P delta (correctionsOf p us)) uu
  let uPre : W128 := ⟨wordAt uu p.labelRowOffset, wordAt uu (p.labelRowOffset + 64)⟩
  fun e => blk 4 (sibAnswers Hs (gammaOf T dbit) (Prover.gateInputsOff p T P.iv cols W128.zero)
    (Prover.gateInputsOff p T P.iv cols uPre))[e.val]!

/-- The tape with its sibling answers replaced by the ones it determines. -/
def fillSib (Hs : Hashes) (T : CrtTables) (st : Statement) (t : IdealTape st.params) :
    IdealTape st.params :=
  (t.1, withSib (dropSib t.2) (sibOf Hs T st t.1 t.2))

/-- `sibOf` with the public values and `Δ` given. -/
def sibOfAt (Hs : Hashes) (T : CrtTables) (st : Statement) (delta : Bytes 16) (P : Pub)
    (t : Pads st.params) : Sib :=
  let p := st.params
  let us := usOf p t
  let uu := us[0]!
  let dbit := BAVC.deltaBit (ba delta)
  let cols := tagCols dbit (qcolsOf st P delta (correctionsOf p us)) uu
  let uPre : W128 := ⟨wordAt uu p.labelRowOffset, wordAt uu (p.labelRowOffset + 64)⟩
  fun e => blk 4 (sibAnswers Hs (gammaOf T dbit) (Prover.gateInputsOff p T P.iv cols W128.zero)
    (Prover.gateInputsOff p T P.iv cols uPre))[e.val]!

lemma sibOf_eq (Hs : Hashes) (T : CrtTables) (st : Statement) (s : Shared) (t : Pads st.params) :
    sibOf Hs T st s t = sibOfAt Hs T st (deltaOf s.2.1) (pubOf Hs st s (deltaOf s.2.1)) t := rfl

lemma usOf_withSib {p : Params} (t : Pads p) (z : Sib) : usOf p (withSib (dropSib t) z) = usOf p t :=
  rfl

lemma sibOf_withSib (Hs : Hashes) (T : CrtTables) (st : Statement) (s : Shared)
    (t : Pads st.params) (z : Sib) : sibOf Hs T st s (withSib (dropSib t) z) = sibOf Hs T st s t := by
  rw [sibOf_eq, sibOf_eq]
  unfold sibOfAt
  dsimp only
  rw [usOf_withSib]

lemma sibOf_withSib' (Hs : Hashes) (T : CrtTables) (st : Statement) (s : Shared)
    (u : PadsU st.params) (z z' : Sib) :
    sibOf Hs T st s (withSib u z) = sibOf Hs T st s (withSib u z') := by
  rw [sibOf_eq, sibOf_eq]
  unfold sibOfAt
  dsimp only
  rw [show usOf st.params (withSib u z) = usOf st.params (withSib u z') from rfl]

/-- The sibling answers of a tape of a hidden part do not matter once they are recomputed. -/
lemma fillSib_tapeOfHidden (Hs : Hashes) (T : CrtTables) (st : Statement) (ivPre : Bytes 16)
    (g : Grind) (hid : Hidden st.params) (z z' : Sib) :
    fillSib Hs T st (tapeOfHidden ivPre g hid z) = fillSib Hs T st (tapeOfHidden ivPre g hid z') := by
  have e : ∀ z, fillSib Hs T st (tapeOfHidden ivPre g hid z) = ((ivPre, g, hid.1, hid.2.1),
      withSib hid.2.2 (sibOf Hs T st (ivPre, g, hid.1, hid.2.1) (withSib hid.2.2 z))) := fun _ => rfl
  rw [e, e, sibOf_withSib' Hs T st _ _ z z']

lemma fillSib_fst (Hs : Hashes) (T : CrtTables) (st : Statement) (t : IdealTape st.params) :
    (fillSib Hs T st t).1 = t.1 := rfl

/-! ## The hybrids -/

/-- `H₃`'s answer at the seed input, as the root seed and `iv_pre`. -/
def h3Seed (Hs : Hashes) (mu1 wPrefix rho : ByteArray) : Bytes 16 × Bytes 16 :=
  let h3 := Hs.hash .h3 ((wPrefix ++ mu1 ++ rho).push 3)
  (blk 16 (h3.extract 0 16), blk 16 (h3.extract 16 32))

/-- Step 1 with the root seed and `iv_pre` `x`. -/
def pendAt (Hs : Hashes) (T : CrtTables) (st : Statement) (wPrefix : ByteArray)
    (x : Bytes 16 × Bytes 16) : Prover.Pending :=
  voleGenAt Hs T st.params (st.mu1 Hs) wPrefix (ba x.1) (ba x.2) st.binder1

lemma pendAt_iv (Hs : Hashes) (T : CrtTables) (st : Statement) (wPrefix : ByteArray)
    (x : Bytes 16 × Bytes 16) :
    (pendAt Hs T st wPrefix x).iv = Hs.hash .h4 ((ba x.2 ++ st.mu1 Hs).push 4) := rfl

lemma voleGen_eq_pendAt (Hs : Hashes) (hHs : HashesWF Hs) (T : CrtTables) (st : Statement)
    (wPrefix rho : ByteArray) :
    Prover.voleGen Hs T st.params (st.mu1 Hs) wPrefix rho st.binder1 =
      pendAt Hs T st wPrefix (h3Seed Hs (st.mu1 Hs) wPrefix rho) := by
  have h32 := hHs .h3 ((wPrefix ++ st.mu1 Hs ++ rho).push 3)
  rw [voleGen_eq_voleGenAt, pendAt, h3Seed, ba_blk_of_size (by rw [ByteArray.size_extract, h32]; rfl),
    ba_blk_of_size (by rw [ByteArray.size_extract, h32]; rfl)]

/-- **The H1 hypothesis**: `H₃`'s answer at the seed input `w_pre ‖ mu ‖ rho ‖ 3`, for uniform
`rho`, is `ε`-close to a uniform root seed and `iv_pre`. -/
def H3Hyp (Hs : Hashes) (mu1 wPrefix : ByteArray) (ε : ℝ) : Prop :=
  Close ε (fun ρ : Bytes 16 => h3Seed Hs mu1 wPrefix (ba ρ)) (id : Bytes 16 × Bytes 16 → _)

/-- **The grinding hypothesis**: the `H₂³` answers at the grinding points of the prefix `pre x`
(a function of the root seed and `iv_pre`) are `ε`-close to uniform answers independent of them. -/
def GrindHyp (Hs : Hashes) (pre : Bytes 16 × Bytes 16 → ByteArray) (ε : ℝ) : Prop :=
  Close ε (fun x : Bytes 16 × Bytes 16 => (x.1, x.2, realGrind Hs (pre x)))
    (id : Bytes 16 × Bytes 16 × Grind → _)

/-- **The H4 hypothesis**: for every 16-byte `iv` and every `Δ`, the hidden part of the commitment
from a uniform root seed is `ε`-close to uniform. -/
def HideHyp (p : Params) (ε : ℝ) : Prop :=
  ∀ (iv : ByteArray) (delta : Bytes 16), iv.size = 16 →
    Close ε (hiddenOut p iv (ba delta)) (hiddenIdeal (p := p) (ba delta))

/-- **The H6 hypothesis**: on a uniform tape, the ideal-tape prover with the sibling answers the
tape determines is `ε`-close to the one with uniform sibling answers. -/
def LabHyp (Hs : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray) (ε : ℝ) : Prop :=
  Close ε (fun t : IdealTape st.params => proveIdeal Hs T st w (fillSib Hs T st t))
    (proveIdeal Hs T st w)

/-! ## The deterministic steps -/

section Steps

variable (Hs : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)

lemma tapeOf_eq_tape1 (hHs : HashesWF Hs) (rho : ByteArray) :
    tapeOf Hs T st w rho = tapeAt Hs T st.params
      (pendAt Hs T st (w.extract 0 st.params.witnessBytes)
        (h3Seed Hs (st.mu1 Hs) (w.extract 0 st.params.witnessBytes) rho))
      (realGrind Hs (realPre Hs st (pendAt Hs T st (w.extract 0 st.params.witnessBytes)
        (h3Seed Hs (st.mu1 Hs) (w.extract 0 st.params.witnessBytes) rho)) w)) := by
  rw [tapeOf_eq_tapeAt, voleGen_eq_pendAt Hs hHs]

/-- The tape of a step 1 at `(seed, iv_pre)` and grinding answers `g`, with the sibling answers
recomputed, is the tape of the hidden part. -/
lemma fillSib_tapeAt (wPrefix : ByteArray) (seed ivPre : Bytes 16) (g : Grind) :
    fillSib Hs T st (tapeAt Hs T st.params (pendAt Hs T st wPrefix (seed, ivPre)) g) =
      fillSib Hs T st (tapeOfHidden ivPre g (hiddenOut st.params
        (pendAt Hs T st wPrefix (seed, ivPre)).iv (ba (deltaOf g)) seed) fun _ => fun _ => 0) := by
  have h : (tapeAt Hs T st.params (pendAt Hs T st wPrefix (seed, ivPre)) g).1 =
      (tapeOfHidden ivPre g (hiddenOut st.params
        (pendAt Hs T st wPrefix (seed, ivPre)).iv (ba (deltaOf g)) seed) fun _ => fun _ => 0).1 := by
    simp only [tapeAt, tapeOfHidden, hiddenOut, pendAt, voleGenAt, deltaOf, blk_ba]
  have h2 : (tapeOfHidden ivPre g (hiddenOut st.params
        (pendAt Hs T st wPrefix (seed, ivPre)).iv (ba (deltaOf g)) seed) fun _ => fun _ => 0).2 =
      withSib (dropSib (tapeAt Hs T st.params (pendAt Hs T st wPrefix (seed, ivPre)) g).2)
        fun _ => fun _ => 0 := rfl
  rw [fillSib, fillSib, ← h, h2, sibOf_withSib]
  rfl

lemma proveIdeal_none {t : IdealTape st.params} (hg : firstHit t.1.2.1 = none) :
    proveIdeal Hs T st w t = if w.size != st.params.witnessBytes then .error "witness: wrong length"
      else .error "grinding failed" := by
  simp only [proveIdeal, hg]

/-- **The real run's sibling answers are the ones its tape determines**, for a step 1 at any
16-byte seed and `iv_pre`, when a grinding answer is accepted. -/
theorem fillSib_tapeAt_eq (hHs : HashesWF Hs) (hbavc : BAVCComplete)
    (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows) (s : Prover.Pending)
    {wPrefix seed ivPre : ByteArray}
    (hs : voleGenAt Hs T st.params (st.mu1 Hs) wPrefix seed ivPre st.binder1 = s)
    (hseed16 : seed.size = 16) (hivp16 : ivPre.size = 16) {g : Grind} {ctr : ℕ} {d : Bytes 16}
    (hg : firstHit g = some (ctr, d)) :
    fillSib Hs T st (tapeAt Hs T st.params s g) = tapeAt Hs T st.params s g := by
  have hd16 : (ba d).size = 16 := size_ba d
  have hcount : openCount (ba d) ≤ 105 := by
    have := firstHit_accepts hg
    simp only [accepts, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    exact this.2
  obtain ⟨opening, hopen⟩ := Option.isSome_iff_exists.1
    (by rw [openAt_isSome]; simpa using hcount : (BAVC.openAt s.tree s.leaves.coms (ba d)).isSome)
  have ht : tapeAt Hs T st.params s g =
      ((blk 16 s.ivPre, g, comsOf s.leaves.coms (ba d), seedsOf s.tree (ba d)),
        realPads Hs T st.params s (ba d)) := by
    simp only [tapeAt, hg, Option.map_some, Option.getD_some]
  have hdel : deltaOf g = d := by simp only [deltaOf, hg, Option.map_some, Option.getD_some]
  rw [ht]
  obtain ⟨hus, hu0, hcorr, -, hPiv, -, hqcols, -, -, -⟩ :=
    step1_realAt Hs T st s hs hseed16 hivp16 hHs hbavc hlab g ctr hd16 hopen
  simp only [blk_ba] at hPiv hqcols
  have spec := voleGenAt_spec Hs T st.params (st.mu1 Hs) wPrefix seed ivPre st.binder1
  rw [hs] at spec
  obtain ⟨-, -, -, -, -, -, -, hsu, -⟩ := spec
  have hsib : sibOf Hs T st (blk 16 s.ivPre, g, comsOf s.leaves.coms (ba d), seedsOf s.tree (ba d))
      (realPads Hs T st.params s (ba d)) = (realPads Hs T st.params s (ba d)).2.2.2.2.2.2 := by
    rw [sibOf_eq]
    have hg2 : (blk 16 s.ivPre, g, comsOf s.leaves.coms (ba d), seedsOf s.tree (ba d)).2.1 = g :=
      rfl
    rw [hg2, hdel]
    unfold sibOfAt
    dsimp only
    rw [hus, hu0, hcorr, hqcols, hPiv]
    have hcongr : ∀ off, Prover.gateInputsOff st.params T s.iv
        (tagCols (BAVC.deltaBit (ba d)) (convertToVoleAt st.params (BAVC.deltaBit (ba d))
          (proverCorr st.params s.iv (leafKey s.leaves)) s.iv (leafKey s.leaves)) s.u) off =
        Prover.gateInputsOff st.params T s.iv
          (Prover.senderColumns st.params s.iv (leafKey s.leaves)) off :=
      fun off => gateInputsOff_congr _ _ _ off fun c hc k hk => by
        rw [hsu]; exact wbit_tagCols _ _ _ _ hc (by omega)
    rw [hcongr, hcongr]
    rfl
  rw [fillSib]
  dsimp only
  rw [hsib]
  rfl

/-- The real run's sibling answers are the ones its tape determines, seen through the ideal-tape
prover (also when no grinding answer is accepted: then the prover refuses). -/
theorem real_fillSib (hHs : HashesWF Hs) (hbavc : BAVCComplete)
    (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows) (s : Prover.Pending)
    {wPrefix seed ivPre : ByteArray}
    (hs : voleGenAt Hs T st.params (st.mu1 Hs) wPrefix seed ivPre st.binder1 = s)
    (hseed16 : seed.size = 16) (hivp16 : ivPre.size = 16) (g : Grind) :
    proveIdeal Hs T st w (fillSib Hs T st (tapeAt Hs T st.params s g)) =
      proveIdeal Hs T st w (tapeAt Hs T st.params s g) := by
  have hg1 : (tapeAt Hs T st.params s g).1.2.1 = g := rfl
  rcases hg : firstHit g with _ | ⟨ctr, d⟩
  · -- No accepted answer: both refuse, whatever the pads.
    rw [proveIdeal_none Hs T st w (by rw [fillSib_fst, hg1, hg]),
      proveIdeal_none Hs T st w (by rw [hg1, hg])]
  · rw [fillSib_tapeAt_eq Hs T st hHs hbavc hlab s hs hseed16 hivp16 hg]

lemma openingOf_zeroTail (delta : ByteArray) (coms : Fin BAVC.tau → Bytes 32)
    (sd : Fin 105 → Bytes 16) : openingOf delta coms (zeroTail delta sd) = openingOf delta coms sd := by
  have h : ∀ acc, (List.range (openCount delta)).foldl (fun acc k => acc ++
      if h : k < 105 then ba (zeroTail delta sd ⟨k, h⟩) else ByteArray.empty) acc =
      (List.range (openCount delta)).foldl (fun acc k => acc ++
      if h : k < 105 then ba (sd ⟨k, h⟩) else ByteArray.empty) acc := fun acc =>
    List.foldl_ext _ _ _ fun acc k hk => by
      have hk := List.mem_range.1 hk
      by_cases h105 : k < 105
      · simp only [h105, dite_true, zeroTail, hk, ite_true]
      · simp only [h105, dite_false]
  simp only [openingOf, h]

/-- `pubOf` from `iv_pre` and the opening. -/
def pubOfAt (ivPre : Bytes 16) (opening : ByteArray) (delta : Bytes 16) : Pub :=
  let mu1 := st.mu1 Hs
  let iv := Hs.hash .h4 ((ba ivPre ++ mu1).push 4)
  let leaves := (BAVC.reconstruct iv opening (ba delta)).getD ⟨.empty, .empty⟩
  { mu1, iv, opening, leaves, check := BAVC.check (Hs.hash .h1) leaves.coms }

lemma pubOf_tuple (a : Bytes 16) (g : Grind) (c : Fin BAVC.tau → Bytes 32)
    (sd : Fin 105 → Bytes 16) (d : Bytes 16) :
    pubOf Hs st (a, g, c, sd) d = pubOfAt Hs st a (openingOf (ba d) c sd) d := rfl

/-- `publicFields` from `iv_pre` and the opening. -/
def publicFieldsAt (a : Bytes 16) (opening : ByteArray) (ctr : ℕ) (delta : Bytes 16) :
    Prover.Fields :=
  { corrections := .empty, cmult := .empty, voleCheck := .empty, correction := .empty,
    qsProof := .empty, opening := opening, delta := ba delta, ivPre := ba a, ctr := ctrBytes ctr }

lemma publicFields_tuple (a : Bytes 16) (g : Grind) (c : Fin BAVC.tau → Bytes 32)
    (sd : Fin 105 → Bytes 16) (ctr : ℕ) (d : Bytes 16) :
    publicFields (a, g, c, sd) ctr d = publicFieldsAt a (openingOf (ba d) c sd) ctr d := rfl

lemma tuple_grind (a : Bytes 16) (g : Grind) (c : Fin BAVC.tau → Bytes 32)
    (sd : Fin 105 → Bytes 16) : ((a, g, c, sd) : Shared).2.1 = g := rfl

/-- The ideal prover reads the shared tape through the public values and the public fields. -/
lemma idealCore_congr {s s' : Shared} {ctr : ℕ} {d : Bytes 16} (t : Pads st.params)
    (h1 : pubOf Hs st s d = pubOf Hs st s' d) (h2 : publicFields s ctr d = publicFields s' ctr d) :
    idealCore Hs T st w s ctr d t = idealCore Hs T st w s' ctr d t := by
  simp only [idealCore, idealTail, tC1, tVRows, tVMask, tUt, tF1, tF0, tCrt, h1, h2]

/-- **The seed slots past the opened ones do not matter.** -/
theorem proveIdeal_fillSib_zeroTail (a : Bytes 16) (g : Grind) (c : Fin BAVC.tau → Bytes 32)
    (sd : Fin 105 → Bytes 16) (t : Pads st.params) :
    proveIdeal Hs T st w (fillSib Hs T st ((a, g, c, zeroTail (ba (deltaOf g)) sd), t)) =
      proveIdeal Hs T st w (fillSib Hs T st ((a, g, c, sd), t)) := by
  have hf : ∀ sd', fillSib Hs T st ((a, g, c, sd'), t) =
      ((a, g, c, sd'), withSib (dropSib t) (sibOf Hs T st (a, g, c, sd') t)) := fun _ => rfl
  rw [hf, hf]
  rcases hg : firstHit g with _ | ⟨ctr, d⟩
  · rw [proveIdeal_none Hs T st w (by rw [tuple_grind, hg]),
      proveIdeal_none Hs T st w (by rw [tuple_grind, hg])]
  · have hdel : deltaOf g = d := by simp only [deltaOf, hg, Option.map_some, Option.getD_some]
    have hsib : sibOf Hs T st (a, g, c, zeroTail (ba (deltaOf g)) sd) t =
        sibOf Hs T st (a, g, c, sd) t := by
      rw [sibOf_eq, sibOf_eq, hdel, pubOf_tuple, pubOf_tuple, openingOf_zeroTail]
    rw [hsib]
    have e1 : ∀ (s' : Shared) (t' : Pads st.params), s'.2.1 = g →
        proveIdeal Hs T st w (s', t') = if w.size != st.params.witnessBytes then
          .error "witness: wrong length" else idealCore Hs T st w s' ctr d t' := by
      intro s' t' hs'
      simp only [proveIdeal, hs', hg]
    rw [e1 _ _ (tuple_grind _ _ _ _), e1 _ _ (tuple_grind _ _ _ _), hdel,
      idealCore_congr Hs T st w (s := (a, g, c, zeroTail (ba d) sd)) (s' := (a, g, c, sd)) _ (by rw [pubOf_tuple, pubOf_tuple, openingOf_zeroTail])
        (by rw [publicFields_tuple, publicFields_tuple, openingOf_zeroTail])]

end Steps

/-! ## The hybrid argument -/

lemma Close.nonneg {α β γ : Type*} [Fintype α] [Fintype β] {ε : ℝ} {X : α → γ} {Y : β → γ}
    (h : Close ε X Y) : 0 ≤ ε :=
  (abs_nonneg _).trans (h fun _ => True)

section Hybrids

variable (Hs : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)

/-- Hybrid 2: uniform root seed and `iv_pre`, the real grinding answers. -/
def hyb1 (x : Bytes 16 × Bytes 16) : Except String ByteArray :=
  proveIdeal Hs T st w (tapeAt Hs T st.params (pendAt Hs T st (w.extract 0 st.params.witnessBytes) x)
    (realGrind Hs (realPre Hs st (pendAt Hs T st (w.extract 0 st.params.witnessBytes) x) w)))

/-- Hybrid 3: uniform root seed, `iv_pre` and grinding answers. -/
def hyb2 (y : Bytes 16 × Bytes 16 × Grind) : Except String ByteArray :=
  proveIdeal Hs T st w (tapeAt Hs T st.params
    (pendAt Hs T st (w.extract 0 st.params.witnessBytes) (y.1, y.2.1)) y.2.2)

/-- Hybrid 4: the hidden part from `hid`, the sibling answers recomputed. -/
def hyb3 (b : Bytes 16 × Grind) (hid : Hidden st.params) : Except String ByteArray :=
  proveIdeal Hs T st w (fillSib Hs T st (tapeOfHidden b.1 b.2 hid fun _ => fun _ => 0))

theorem hop_h1 (hHs : HashesWF Hs) {ε : ℝ}
    (h : H3Hyp Hs (st.mu1 Hs) (w.extract 0 st.params.witnessBytes) ε) :
    Close ε (fun ρ : Bytes 16 => proveIdeal Hs T st w (tapeOf Hs T st w (ba ρ))) (hyb1 Hs T st w) :=
  (h.map (hyb1 Hs T st w)).congr (fun ρ => by rw [tapeOf_eq_tape1 Hs T st w hHs]; rfl) fun _ => rfl

theorem hop_grind {ε : ℝ} (h : GrindHyp Hs (fun x => realPre Hs st
      (pendAt Hs T st (w.extract 0 st.params.witnessBytes) x) w) ε) :
    Close ε (hyb1 Hs T st w) (hyb2 Hs T st w) :=
  (h.map (hyb2 Hs T st w)).congr (fun _ => rfl) fun _ => rfl

theorem hop_hide (hHs : HashesWF Hs) (hbavc : BAVCComplete)
    (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows) {ε : ℝ}
    (h : HideHyp st.params ε) :
    Close ε (hyb2 Hs T st w) (fun y : Hidden st.params × (Bytes 16 × Grind) =>
      hyb3 Hs T st w y.2 (hiddenIdeal (ba (deltaOf y.2.2)) y.1)) := by
  let wP := w.extract 0 st.params.witnessBytes
  let ivOf : Bytes 16 → ByteArray := fun ivPre => Hs.hash .h4 ((ba ivPre ++ st.mu1 Hs).push 4)
  have hb : ∀ b : Bytes 16 × Grind, Close ε
      (fun seed : Bytes 16 => hyb3 Hs T st w b (hiddenOut st.params (ivOf b.1) (ba (deltaOf b.2)) seed))
      (fun hid : Hidden st.params => hyb3 Hs T st w b (hiddenIdeal (ba (deltaOf b.2)) hid)) :=
    fun b => (h (ivOf b.1) (deltaOf b.2) (hHs .h4 _)).map (hyb3 Hs T st w b)
  refine (Close.prod_left (X := fun (seed : Bytes 16) (b : Bytes 16 × Grind) =>
      hyb3 Hs T st w b (hiddenOut st.params (ivOf b.1) (ba (deltaOf b.2)) seed))
    (Y := fun (hid : Hidden st.params) (b : Bytes 16 × Grind) =>
      hyb3 Hs T st w b (hiddenIdeal (ba (deltaOf b.2)) hid)) hb).congr (fun y => ?_) fun _ => rfl
  rw [hyb2, ← real_fillSib Hs T st w hHs hbavc hlab (pendAt Hs T st wP (y.1, y.2.1)) rfl
    (size_ba _) (size_ba _), fillSib_tapeAt Hs T st wP y.1 y.2.1 y.2.2, pendAt_iv]
  rfl

lemma hyb3_zeroTail (b : Bytes 16 × Grind) (hid : Hidden st.params) :
    hyb3 Hs T st w b (hiddenIdeal (ba (deltaOf b.2)) hid) = hyb3 Hs T st w b hid := by
  -- Destructured, so that the kernel never compares two projections of different tuples.
  obtain ⟨a, g⟩ := b
  obtain ⟨c, sd, u⟩ := hid
  have e1 : tapeOfHidden a g (hiddenIdeal (ba (deltaOf g)) (c, sd, u)) (fun _ => fun _ => 0) =
      ((a, g, c, zeroTail (ba (deltaOf g)) sd), withSib u fun _ => fun _ => 0) := rfl
  have e2 : tapeOfHidden a g (c, sd, u) (fun _ => fun _ => 0) =
      ((a, g, c, sd), withSib u fun _ => fun _ => 0) := rfl
  rw [hyb3, hyb3, e1, e2, proveIdeal_fillSib_zeroTail]

theorem hop_tail :
    Close 0 (fun y : Hidden st.params × (Bytes 16 × Grind) =>
      hyb3 Hs T st w y.2 (hiddenIdeal (ba (deltaOf y.2.2)) y.1))
      (fun y : Hidden st.params × (Bytes 16 × Grind) => hyb3 Hs T st w y.2 y.1) :=
  (close_self le_rfl _).congr (fun y => hyb3_zeroTail Hs T st w y.2 y.1) fun _ => rfl

theorem hop_tape :
    Close 0 (fun y : Hidden st.params × (Bytes 16 × Grind) => hyb3 Hs T st w y.2 y.1)
      (fun t : IdealTape st.params => proveIdeal Hs T st w (fillSib Hs T st t)) := by
  have e1 : Close 0 (fun x : (Hidden st.params × (Bytes 16 × Grind)) × Sib =>
      hyb3 Hs T st w x.1.2 x.1.1)
      (fun y : Hidden st.params × (Bytes 16 × Grind) => hyb3 Hs T st w y.2 y.1) :=
    close_prod_fst (X := fun y : Hidden st.params × (Bytes 16 × Grind) => hyb3 Hs T st w y.2 y.1)
  have e2 : Close 0 (fun x : (Hidden st.params × (Bytes 16 × Grind)) × Sib =>
      proveIdeal Hs T st w (fillSib Hs T st (tapeEquiv st.params x)))
      (fun t : IdealTape st.params => proveIdeal Hs T st w (fillSib Hs T st t)) :=
    close_equiv (tapeEquiv st.params) (fun t => proveIdeal Hs T st w (fillSib Hs T st t))
  have e3 : ∀ x : (Hidden st.params × (Bytes 16 × Grind)) × Sib,
      proveIdeal Hs T st w (fillSib Hs T st (tapeEquiv st.params x)) = hyb3 Hs T st w x.1.2 x.1.1 :=
    fun x => by
      rw [hyb3, show tapeEquiv st.params x = tapeOfHidden x.1.2.1 x.1.2.2 x.1.1 x.2 from rfl,
        fillSib_tapeOfHidden Hs T st _ _ _ x.2 fun _ => fun _ => 0]
  exact ((e1.symm.trans (e2.congr e3 fun _ => rfl)).mono (by norm_num))

/-- **The hop hypotheses of one statement and witness**, with their errors: H1 (`ε_rho`), the
grinding answers (`ε_grind`), H4 (`ε_bavc`, BAVC hiding: `ε_hide` of `lean/docs/zk.md` §3) and H6
(`ε_lab`). -/
structure HopHyps (Hs : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)
    (εrho εgrind εbavc εlab : ℝ) : Prop where
  rho : H3Hyp Hs (st.mu1 Hs) (w.extract 0 st.params.witnessBytes) εrho
  grind : GrindHyp Hs (fun x => realPre Hs st
    (pendAt Hs T st (w.extract 0 st.params.witnessBytes) x) w) εgrind
  bavc : HideHyp st.params εbavc
  lab : LabHyp Hs T st w εlab

/-- **The tape hypothesis from one hypothesis per hop**: the real run's tape, seen through the
ideal-tape prover, is `(ε_rho + ε_grind + ε_bavc + ε_lab)`-close to a uniform ideal tape. -/
theorem tape_close_of_hops (hHs : HashesWF Hs) (hbavc : BAVCComplete)
    (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    {εrho εgrind εbavc εlab : ℝ} (h : HopHyps Hs T st w εrho εgrind εbavc εlab) :
    Close (εrho + εgrind + εbavc + εlab)
      (fun ρ : Bytes 16 => proveIdeal Hs T st w (tapeOf Hs T st w (ba ρ)))
      (proveIdeal Hs T st w) := by
  have hnn := Close.nonneg (h.bavc (Prover.zeros 16) (fun _ => 0) (zeros_size _))
  have := (((((hop_h1 Hs T st w hHs h.rho).trans (hop_grind Hs T st w h.grind)).trans
    (hop_hide Hs T st w hHs hbavc hlab h.bavc)).trans (hop_tail Hs T st w)).trans
    (hop_tape Hs T st w)).trans h.lab
  exact this.mono (by linarith)

end Hybrids

end VoleMole.ZK.Sim
