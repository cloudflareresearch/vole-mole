import VoleMole.ZK.HopsH6
import VoleMole.ZK.HopsH4Ideal

/-!
# The hops composed in one random-oracle and ideal-cipher experiment (`lean/docs/zk.md` §10.1)

`ZK/Hops.lean` composes one hypothesis per hop for a *fixed* hash record and AES
(`tape_close_of_hops`). The hops are proved separately in idealized models, each with its own
uniform table: H1 and grinding (`ZK/HopsROM.lean`), H6 (`ZK/HopsH6.lean`), H4
(`ZK/HopsH4Ideal.lean`). Here they are composed into **one experiment** with all the tables drawn
independently and a distinguisher that reads them.

**The model.**
* The hash record is `recOf Hb … pre G3 G2 G5`: a base record `Hb` (SHAKE for the KATs) with three
  domains answered by independent uniform tables on the inputs the hops read: `H₃` at the seed
  inputs `w_pre ‖ mu ‖ rho ‖ 3` (`G3`, keys `rho`), `H₂³` at the grinding points
  `pre(seed, iv_pre) ‖ c ‖ 11` (`G2`, keys `(seed, iv_pre, c)`), `H₅` at the sibling inputs
  (`G5`, keys a tape and a gate). Every other domain (`mu`, `H₁`, `H₄`, `H₂¹`, `H₂²`, the
  combination), and these three off the tables' inputs, are `Hb`'s.
* The BAVC's cipher is a uniform table `E` (`Cipher`, rows uniform functions). The prover with the
  cipher as a parameter is the proof-only `proveE`: the hidden part of the commitment (the hidden
  leaves' commitments, the opened seeds, all `u^{(i)}` and `u_hi`) is `hiddenOutE E`; the rest of
  the proof is computed from it as by the executable prover (`hyb3`: the ideal-tape prover, which
  recomputes the public part, the opened subtrees, with AES); the grinding prefix is a parameter
  `pre`, which may depend on `G5` and `E`. **`proveE_aes`**, **`proveE_recOf_aes`**: at
  `E = AES` with the executable prefix (`preReal`) it is the executable prover with the record.

**`zk_rom_ic`.** For a statement with dedicated label rows and a witness satisfying the
deterministic hypotheses (`ZKHyp`), parameters with fewer than `2³²` blocks per PRG call
(`SmallParams`) and any prefix family `pre`: a distinguisher that sees the proof and the tables
`G3`, `G5`, `E`, and reads them adaptively at `q₃`, `q₅`, `q_E` keys, tells `proveE` (uniform
`rho`, `G3`, `G2`, `G5`, `E`) from the simulator `simulate` (with independent uniform `G3`, `G5`,
`E`) with advantage at most

    q₃·2⁻¹²⁸ + 0 + 221·(4607 + q_E)·2⁻¹²⁸ + (q₅ + 1)·2⁻¹²⁸

(H1, grinding, H4, H6). The hybrids are those of `tape_close_of_hops`, each hop instantiated by
its idealized version with the other tables fixed and averaged over (`joint_h1`, `joint_grind`,
`joint_h4`, `joint_tape`, `joint_h6`, `joint_sim`). What makes the averaging possible: the
ideal-tape prover reads neither `H₃` nor `H₂³` (`proveIdeal_agreeOff`, `fillSib_agreeOff`), and the
`H₅` table's encoding does not depend on the other tables (`sEnc_agreeOff`).

**Not covered.** The distinguisher does not read `H₂³`: with `H₂³` access the simulator must
program `H₂³` at the proof's grinding points (`simulateRO`), and linking those points (computed
from the output) to the prover's (`pre` of the coins), through the hybrids after H4, is not done
here; `ZK/HopsH23.lean` (`zk_rom_h23`) does it for the executable prover, with BAVC hiding for AES
assumed. The public part of the commitment is recomputed with AES, not `E` (a fully
cipher-parametric prover would add those reads to `q_E`). One proof (no `ε_iv`, `rho`-collision or `ε_prog` terms);
the rows are functions, not permutations (the PRP/PRF switching term is on paper); SHAKE as a
random oracle and AES as an ideal cipher are the modelling steps.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy

/-! ## Records that differ in a domain the prover does not read -/

section Congr

lemma _root_.VoleMole.Verifier.Hashes.AgreeOff.symm {k : Kind} {Hs Hs' : Hashes}
    (h : Hs.AgreeOff k Hs') : Hs'.AgreeOff k Hs := fun k' hk => (h k' hk).symm

lemma _root_.VoleMole.Verifier.Hashes.AgreeOff.trans {k : Kind} {Hs Hs' Hs'' : Hashes}
    (h : Hs.AgreeOff k Hs') (h' : Hs'.AgreeOff k Hs'') : Hs.AgreeOff k Hs'' :=
  fun k' hk => (h k' hk).trans (h' k' hk)

/-- A table on the same domain on top of two records that agree off it. -/
lemma _root_.VoleMole.Verifier.Hashes.AgreeOff.withTable_same {k : Kind} {Hs Hs' : Hashes}
    (h : Hs.AgreeOff k Hs') {K K' : Type} (enc : K → ByteArray) (enc' : K' → ByteArray)
    (G : K → Bytes k.outLen) (G' : K' → Bytes k.outLen) :
    (Hs.withTable k enc G).AgreeOff k (Hs'.withTable k enc' G') := fun k' hk => by
  funext x
  rw [Hashes.withTable_ne _ _ _ hk, Hashes.withTable_ne _ _ _ hk, h k' hk]

/-- A table on another domain on top of two records that agree off `k`. -/
lemma _root_.VoleMole.Verifier.Hashes.AgreeOff.withTable_other {k k' : Kind} {Hs Hs' : Hashes}
    (h : Hs.AgreeOff k Hs') (hk : k' ≠ k) {K : Type} (enc : K → ByteArray)
    (G : K → Bytes k'.outLen) : (Hs.withTable k' enc G).AgreeOff k (Hs'.withTable k' enc G) :=
  fun k'' hk'' => by
    funext x
    simp only [Hashes.withTable]
    split_ifs with h1 h2
    · rfl
    · rw [h k' hk]
    · rw [h k'' hk'']

/-- **The domains the ideal-tape prover does not read**: neither `H₃` nor `H₂³` (it reads `mu`,
`H₄`, `H₁`, `H₂¹`, `H₂²`, the combination and `H₅`). -/
def Unread (k : Kind) : Prop :=
  k ≠ .mu ∧ k ≠ .muDelayed ∧ k ≠ .h4 ∧ k ≠ .h1 ∧ k ≠ .h21 ∧ k ≠ .h22 ∧ k ≠ .h5 ∧
    ∀ M, k ≠ .comb M

lemma unread_h3 : Unread .h3 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, fun _ => nofun⟩

lemma unread_h23 : Unread .h23 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, fun _ => nofun⟩

variable {k : Kind} {Hs Hs' : Hashes} (hu : Unread k) (h : Hs.AgreeOff k Hs')
  (T : CrtTables) (st : Statement) (w : ByteArray)
include hu h

lemma _root_.VoleMole.Verifier.Hashes.AgreeOff.pubOf' : pubOf Hs st = pubOf Hs' st :=
  h.pubOf hu.1 hu.2.1 hu.2.2.1 hu.2.2.2.1 st

lemma _root_.VoleMole.Verifier.Hashes.AgreeOff.mu1' : st.mu1 Hs = st.mu1 Hs' :=
  h.mu1 hu.1 hu.2.1 st

/-- **The ideal-tape prover does not read an unread domain.** -/
theorem proveIdeal_agreeOff : proveIdeal Hs T st w = proveIdeal Hs' T st w := by
  have hP := h.pubOf' hu st
  have h5 := h .h5 (Ne.symm hu.2.2.2.2.2.2.1)
  have hc1 := h.chal1 hu.2.2.2.2.1
  have hc2 := h.chal2 hu.2.2.2.2.2.1
  have hmd := h.muDelayed hu.1 st
  have hcb := h.combBytes hu.2.2.2.2.2.2.2 st
  funext x
  simp only [proveIdeal, idealCore, idealTail, cmultIdeal, gateHashesIdeal, tCrt, tVRows, tVMask,
    tUt, tC1, hP, h5, hc1, hc2, hmd, hcb]

/-- The sibling answers a tape determines do not read an unread domain. -/
theorem fillSib_agreeOff : fillSib Hs T st = fillSib Hs' T st := by
  have hP := h.pubOf' hu st
  have h5 := h .h5 (Ne.symm hu.2.2.2.2.2.2.1)
  funext x
  simp only [fillSib, sibOf, sibAnswers, hP, h5]

theorem hyb3_agreeOff : hyb3 Hs T st w = hyb3 Hs' T st w := by
  funext b hid
  simp only [hyb3, proveIdeal_agreeOff hu h, fillSib_agreeOff hu h]

/-- Step 1 does not read an unread domain. -/
lemma pendAt_agreeOff (wPrefix : ByteArray) (x : Bytes 16 × Bytes 16) :
    pendAt Hs T st wPrefix x = pendAt Hs' T st wPrefix x := by
  simp only [pendAt, voleGenAt, h.mu1' hu st, h .h4 (Ne.symm hu.2.2.1), h .h1 (Ne.symm hu.2.2.2.1),
    h .h5 (Ne.symm hu.2.2.2.2.2.2.1), h.chal1 hu.2.2.2.2.1]

/-- The grinding prefix does not read an unread domain. -/
lemma prePrefix_agreeOff : prePrefix Hs T st w = prePrefix Hs' T st w := by
  funext x
  simp only [prePrefix, pendAt_agreeOff hu h T st, realPre, realC2, h.chal2 hu.2.2.2.2.2.1,
    h.muDelayed hu.1 st, h.combBytes hu.2.2.2.2.2.2.2 st]

lemma sEnc_agreeOff : sEnc Hs T st = sEnc Hs' T st := by
  funext x
  simp only [sEnc, sibInput, h.pubOf' hu st]

end Congr


/-! ## The cipher-parametric prover -/

section ProveE

variable (Hs : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)

/-- `iv = H₄(iv_pre ‖ mu ‖ 4)`. -/
def ivOfPre (ivPre : Bytes 16) : ByteArray := Hs.hash .h4 ((ba ivPre ++ st.mu1 Hs).push 4)

/-- **The real run from the root seed and `iv_pre` `x`, with the BAVC's cipher `E`**: the grinding
answers at the prefix `pre x`, the hidden part of the commitment computed with `E`
(`hiddenOutE`), and the rest of the proof from them (the ideal-tape prover on the tape with the
sibling answers recomputed, `hyb3`; it recomputes the public part of the commitment, the opened
subtrees, with AES). -/
noncomputable def runE (E : Cipher) (pre : Bytes 16 × Bytes 16 → ByteArray)
    (x : Bytes 16 × Bytes 16) : Except String ByteArray :=
  hyb3 Hs T st w (x.2, realGrind Hs (pre x))
    (hiddenOutE E st.params (ivOfPre Hs st x.2) (ba (deltaOf (realGrind Hs (pre x)))) x.1)

/-- **The cipher-parametric prover** (proof only): `H₃`'s seed and `iv_pre` from `rho`, then
`runE`. At `E = AES` and the prover's own grinding prefix it is the executable prover
(`proveE_aes`). -/
noncomputable def proveE (E : Cipher) (pre : Bytes 16 × Bytes 16 → ByteArray) (ρ : Bytes 16) :
    Except String ByteArray :=
  runE Hs T st w E pre (h3Seed Hs (st.mu1 Hs) (w.extract 0 st.params.witnessBytes) (ba ρ))

/-- **The bridge: `proveE` at AES is the executable prover.** -/
theorem proveE_aes {cs : ByteArray → ByteArray → System GF128} (h : RunHyp Hs T st w cs)
    (ρ : Bytes 16) :
    proveE Hs T st w aesTable (prePrefix Hs T st w) ρ = Prover.prove Hs T st w (ba ρ) := by
  let wP := w.extract 0 st.params.witnessBytes
  rw [prove_eq_proveIdeal Hs T st w (ba ρ) cs h.zk.q h.hHs h.hbavc (h.hcrt _) h.hlab,
    tapeOf_eq_tape1 Hs T st w h.hHs]
  rw [proveE]
  generalize h3Seed Hs (st.mu1 Hs) (w.extract 0 st.params.witnessBytes) (ba ρ) = y
  rw [← real_fillSib Hs T st w h.hHs h.hbavc h.hlab (pendAt Hs T st wP (y.1, y.2)) rfl
    (size_ba _) (size_ba _), fillSib_tapeAt Hs T st wP y.1 y.2, pendAt_iv]
  simp only [runE, hyb3, prePrefix, ivOfPre, hiddenOut_eq]

end ProveE

/-! ## The record with the three random-oracle tables -/

section Record

variable (Hb : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)

/-- The `H₃` table (keys: `rho`, encoded as the seed input). -/
abbrev Tab3 := Bytes 16 → Bytes 32
/-- The `H₂³` table (keys: the coins and a counter, encoded as the grinding point). -/
abbrev Tab2 := GKey → Bytes 16
/-- The `H₅` table (keys: a tape and a gate, encoded as the gate's sibling input). -/
abbrev Tab5 (p : Params) := SKey p → Bytes 4

/-- **The hash record of the random-oracle model**: the base record `Hb` with `H₃` answered by
`G3` at the seed inputs, `H₂³` by `G2` at the grinding points of the prefix `pre`, and `H₅` by `G5`
at the sibling inputs (`Hb` elsewhere). -/
noncomputable def recOf (pre : Bytes 16 × Bytes 16 → ByteArray) (G3 : Tab3) (G2 : Tab2)
    (G5 : Tab5 st.params) : Hashes :=
  ((Hb.withTable .h3 (seedInput (st.mu1 Hb) (w.extract 0 st.params.witnessBytes)) G3).withTable
    .h23 (gEnc pre) G2).withTable .h5 (sEnc Hb T st) G5

variable {Hb T st w}

lemma recOf_hash_ne {pre : Bytes 16 × Bytes 16 → ByteArray} {G3 : Tab3} {G2 : Tab2}
    {G5 : Tab5 st.params} {k : Kind} (h3 : k ≠ .h3) (h23 : k ≠ .h23) (h5 : k ≠ .h5) :
    (recOf Hb T st w pre G3 G2 G5).hash k = Hb.hash k := by
  funext x
  simp only [recOf, Hashes.withTable, h3, h23, h5, ite_false]

lemma recOf_mu1 (pre : Bytes 16 × Bytes 16 → ByteArray) (G3 : Tab3) (G2 : Tab2)
    (G5 : Tab5 st.params) : st.mu1 (recOf Hb T st w pre G3 G2 G5) = st.mu1 Hb := by
  simp only [Statement.mu1, mu, recOf_hash_ne (k := .mu) (by decide) (by decide) (by decide),
    recOf_hash_ne (k := .muDelayed) (by decide) (by decide) (by decide)]

lemma h3Seed_congr {Hs Hs' : Hashes} (h : Hs.hash .h3 = Hs'.hash .h3) : h3Seed Hs = h3Seed Hs' := by
  funext a b c
  simp only [h3Seed, h]

lemma realGrind_congr {Hs Hs' : Hashes} (h : Hs.hash .h23 = Hs'.hash .h23) :
    realGrind Hs = realGrind Hs' := by
  funext a c
  simp only [realGrind, h]

/-- With the record's `H₃` table, the seed and `iv_pre` of `rho` are the table's answer. -/
lemma recOf_h3Seed (pre : Bytes 16 × Bytes 16 → ByteArray) (G3 : Tab3) (G2 : Tab2)
    (G5 : Tab5 st.params) (ρ : Bytes 16) :
    h3Seed (recOf Hb T st w pre G3 G2 G5) (st.mu1 (recOf Hb T st w pre G3 G2 G5))
      (w.extract 0 st.params.witnessBytes) (ba ρ) = splitSeed (G3 ρ) := by
  rw [recOf_mu1, h3Seed_congr (Hs' := Hb.withTable .h3 (seedInput (st.mu1 Hb)
    (w.extract 0 st.params.witnessBytes)) G3), h3Seed_withTable]
  funext x
  simp only [recOf, Hashes.withTable, reduceCtorEq, ite_false]

/-- With the record's `H₂³` table, the grinding answers are the table's. -/
lemma recOf_realGrind (pre : Bytes 16 × Bytes 16 → ByteArray) (G3 : Tab3) (G2 : Tab2)
    (G5 : Tab5 st.params) (x : Bytes 16 × Bytes 16) :
    realGrind (recOf Hb T st w pre G3 G2 G5) (pre x) = G2 ∘ grindKey pre x := by
  rw [realGrind_congr (Hs' := (Hb.withTable .h3 (seedInput (st.mu1 Hb)
    (w.extract 0 st.params.witnessBytes)) G3).withTable .h23 (gEnc pre) G2), realGrind_withTable]
  funext y
  simp only [recOf, Hashes.withTable, reduceCtorEq, ite_false]

lemma recOf_agreeOff_h3 (pre : Bytes 16 × Bytes 16 → ByteArray) (G3 G3' : Tab3) (G2 : Tab2)
    (G5 : Tab5 st.params) :
    (recOf Hb T st w pre G3 G2 G5).AgreeOff .h3 (recOf Hb T st w pre G3' G2 G5) := by
  intro k hk
  funext x
  by_cases h5 : k = .h5
  · subst h5; simp only [recOf, Hashes.withTable, reduceCtorEq, ite_true, ite_false]
  by_cases h23 : k = .h23
  · subst h23; simp only [recOf, Hashes.withTable, reduceCtorEq, ite_true, ite_false]
  · simp only [recOf, Hashes.withTable, h5, h23, hk, ite_false]

lemma recOf_agreeOff_h23 (pre pre' : Bytes 16 × Bytes 16 → ByteArray) (G3 : Tab3) (G2 G2' : Tab2)
    (G5 : Tab5 st.params) :
    (recOf Hb T st w pre G3 G2 G5).AgreeOff .h23 (recOf Hb T st w pre' G3 G2' G5) := by
  intro k hk
  funext x
  by_cases h5 : k = .h5
  · subst h5; simp only [recOf, Hashes.withTable, reduceCtorEq, ite_true, ite_false]
  by_cases h3 : k = .h3
  · subst h3; simp only [recOf, Hashes.withTable, reduceCtorEq, ite_true, ite_false]
  · simp only [recOf, Hashes.withTable, h5, h3, hk, ite_false]

end Record


/-! ## The hybrids, with the tables the distinguisher reads -/

/-- **Averaging over tables the hop does not touch**: a hop that holds for every value `v` of the
tables the distinguisher reads holds for a distinguisher that reads them. -/
lemma abs_pr_vis_le {M M' V O : Type*} [Fintype M] [Fintype M'] [Fintype V] [Nonempty V]
    {ε : ℝ} {X : M → V → O} {Y : M' → V → O} (h : ∀ v, Close ε (fun m => X m v) (fun m => Y m v))
    (D : O → V → Prop) :
    |pr (M × V) (fun c => D (X c.1 c.2) c.2) - pr (M' × V) (fun c => D (Y c.1 c.2) c.2)| ≤ ε :=
  abs_pr_prod_sub_le' _ _ fun v => h v (fun o => D o v)

section Chain

variable (Hb : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)

/-- **The tables the distinguisher reads**: `H₃`, `H₅` and the cipher. -/
abbrev Vis (p : Params) := Tab3 × (Tab5 p × Cipher)

/-- The record after the grinding hop (whose `H₂³` table is no longer read). -/
noncomputable def recP (G3 : Tab3) (G5 : Tab5 st.params) : Hashes :=
  recOf Hb T st w (fun _ => ByteArray.empty) G3 (fun _ => 0) G5

variable {Hb T st w}

lemma ivOfPre_agreeOff {k : Kind} {Hs Hs' : Hashes} (hu : Unread k) (h : Hs.AgreeOff k Hs') :
    ivOfPre Hs st = ivOfPre Hs' st := by
  funext a
  simp only [ivOfPre, h .h4 (Ne.symm hu.2.2.1), h.mu1' hu st]

lemma recOf_ivOfPre (pre : Bytes 16 × Bytes 16 → ByteArray) (G3 : Tab3) (G2 : Tab2)
    (G5 : Tab5 st.params) : ivOfPre (recOf Hb T st w pre G3 G2 G5) st = ivOfPre Hb st := by
  funext a
  simp only [ivOfPre, recOf_mu1, recOf_hash_ne (k := .h4) (by decide) (by decide) (by decide)]

lemma runE_agreeOff_h3 {Hs Hs' : Hashes} (h : Hs.AgreeOff .h3 Hs') :
    runE Hs T st w = runE Hs' T st w := by
  funext E pre x
  simp only [runE, hyb3_agreeOff unread_h3 h, ivOfPre_agreeOff unread_h3 h,
    realGrind_congr (h .h23 (by decide))]

/-- `recP` is the `H₅` table on top of a record (`HopsH6.H5`), for `lab_rom_hyp`. -/
lemma recP_eq_H5 (G3 : Tab3) (G5 : Tab5 st.params) :
    recP Hb T st w G3 G5 = H5 ((Hb.withTable .h3 (seedInput (st.mu1 Hb)
      (w.extract 0 st.params.witnessBytes)) G3).withTable .h23 (gEnc fun _ => ByteArray.empty)
      fun _ => 0) T st G5 := by
  have h1 := Hb.agreeOff_withTable .h3 (seedInput (st.mu1 Hb) (w.extract 0 st.params.witnessBytes)) G3
  have h2 := (Hb.withTable .h3 (seedInput (st.mu1 Hb) (w.extract 0 st.params.witnessBytes)) G3
    ).agreeOff_withTable .h23 (gEnc fun _ => ByteArray.empty) (fun _ => 0)
  rw [recP, recOf, H5, sEnc_agreeOff unread_h3 h1, sEnc_agreeOff unread_h23 h2]
  rfl

variable (Hb T st w)

/-- **H1 with the tables**: `rho` and the `H₃` table against a uniform seed and `iv_pre`, for a
distinguisher that reads the `H₃` table at `q₃` keys (and the other tables freely). -/
theorem joint_h1 (pre : Tab5 st.params → Cipher → Bytes 16 × Bytes 16 → ByteArray)
    (D : Except String ByteArray → Vis st.params → Prop)
    (Q3 : Except String ByteArray → Tab3 → Tab5 st.params → Cipher → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G5 E, (∀ k ∈ Q3 o G3 G5 E, G3 k = G3' k) →
      (D o (G3, G5, E) ↔ D o (G3', G5, E)))
    {q3 : ℕ} (hq3 : ∀ o G3 G5 E, (Q3 o G3 G5 E).card ≤ q3) :
    |pr ((Bytes 16 × Tab2) × Vis st.params) (fun c =>
        D (proveE (recOf Hb T st w (pre c.2.2.1 c.2.2.2) c.2.1 c.1.2 c.2.2.1) T st w c.2.2.2
          (pre c.2.2.1 c.2.2.2) c.1.1) c.2) -
      pr (((Bytes 16 × Bytes 16) × Tab2) × Vis st.params) (fun c =>
        D (runE (recOf Hb T st w (pre c.2.2.1 c.2.2.2) c.2.1 c.1.2 c.2.2.1) T st w c.2.2.2
          (pre c.2.2.1 c.2.2.2) c.1.1) c.2)| ≤ q3 / 2 ^ 128 := by
  let wP := w.extract 0 st.params.witnessBytes
  let E0 : (Tab2 × (Tab5 st.params × Cipher)) × (Bytes 16 × Tab3) ≃
      (Bytes 16 × Tab2) × Vis st.params :=
    { toFun := fun c => ((c.2.1, c.1.1), (c.2.2, c.1.2))
      invFun := fun c => ((c.1.2, c.2.2), (c.1.1, c.2.1))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let E1 : (Tab2 × (Tab5 st.params × Cipher)) × (Tab3 × (Bytes 16 × Bytes 16)) ≃
      ((Bytes 16 × Bytes 16) × Tab2) × Vis st.params :=
    { toFun := fun c => ((c.2.2, c.1.1), (c.2.1, c.1.2))
      invFun := fun c => ((c.1.2, c.2.2), (c.2.1, c.1.1))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv E0, ← pr_equiv E1]
  refine abs_pr_prod_sub_le _ _ fun a => ?_
  obtain ⟨G2, G5, E⟩ := a
  -- The run after the seed, with a fixed `H₃` table (it does not read `H₃`).
  let R : Bytes 16 × Bytes 16 → Except String ByteArray :=
    runE (recOf Hb T st w (pre G5 E) (fun _ => 0) G2 G5) T st w E (pre G5 E)
  have hR : ∀ G3 : Tab3, runE (recOf Hb T st w (pre G5 E) G3 G2 G5) T st w E (pre G5 E) = R :=
    fun G3 => by rw [runE_agreeOff_h3 (recOf_agreeOff_h3 _ G3 _ G2 G5)]
  let A : Bytes 16 × Bytes 16 → Tab3 → Prop := fun v G3 => D (R v) (G3, G5, E)
  have h := h3_rom_query (st.mu1 Hb) wP Hb A (fun v G3 => Q3 (R v) G3 G5 E)
    (fun v G3 G3' hk => hQ3 (R v) G3 G3' G5 E hk) (fun v G3 => hq3 _ G3 G5 E)
  have e1 : pr (Bytes 16 × Tab3) (fun b => D (proveE (recOf Hb T st w (pre G5 E) b.2 G2 G5) T st w
      E (pre G5 E) b.1) (b.2, G5, E)) = pr (Bytes 16 × (Bytes 16 → Bytes 32)) (fun p =>
        A (h3Seed (Hb.withTable .h3 (seedInput (st.mu1 Hb) wP) p.2) (st.mu1 Hb) wP (ba p.1)) p.2) := by
    refine pr_congr fun b => ?_
    simp only [A, proveE, recOf_h3Seed, h3Seed_withTable, hR]
  have e2 : pr (Bytes 16 × ((Bytes 16 → Bytes 32) × Bytes 32)) (fun p => A (splitSeed p.2.2) p.2.1) =
      pr (Tab3 × (Bytes 16 × Bytes 16)) (fun b => D (runE (recOf Hb T st w (pre G5 E) b.1 G2 G5)
        T st w E (pre G5 E) b.2) (b.1, G5, E)) := by
    rw [pr_prod_snd (α := Bytes 16) (fun q : (Bytes 16 → Bytes 32) × Bytes 32 => A (splitSeed q.2) q.1),
      ← pr_equiv (Equiv.prodCongr (Equiv.refl Tab3) splitEquiv)]
    refine pr_congr fun b => ?_
    simp only [A, hR]
    rfl
  have e1' : pr (Bytes 16 × Tab3) (fun b => D (proveE (recOf Hb T st w (pre G5 E) b.2 G2 G5) T st w
      E (pre G5 E) b.1) (b.2, G5, E)) = pr (Bytes 16 × Tab3) (fun b =>
        D (proveE (recOf Hb T st w (pre (E0 ((G2, G5, E), b)).2.2.1 (E0 ((G2, G5, E), b)).2.2.2)
          (E0 ((G2, G5, E), b)).2.1 (E0 ((G2, G5, E), b)).1.2 (E0 ((G2, G5, E), b)).2.2.1) T st w
          (E0 ((G2, G5, E), b)).2.2.2 (pre (E0 ((G2, G5, E), b)).2.2.1 (E0 ((G2, G5, E), b)).2.2.2)
          (E0 ((G2, G5, E), b)).1.1) (E0 ((G2, G5, E), b)).2) := rfl
  have e2' : pr (Tab3 × (Bytes 16 × Bytes 16)) (fun b => D (runE (recOf Hb T st w (pre G5 E) b.1 G2 G5)
        T st w E (pre G5 E) b.2) (b.1, G5, E)) = pr (Tab3 × (Bytes 16 × Bytes 16)) (fun b =>
        D (runE (recOf Hb T st w (pre (E1 ((G2, G5, E), b)).2.2.1 (E1 ((G2, G5, E), b)).2.2.2)
          (E1 ((G2, G5, E), b)).2.1 (E1 ((G2, G5, E), b)).1.2 (E1 ((G2, G5, E), b)).2.2.1) T st w
          (E1 ((G2, G5, E), b)).2.2.2 (pre (E1 ((G2, G5, E), b)).2.2.1 (E1 ((G2, G5, E), b)).2.2.2)
          (E1 ((G2, G5, E), b)).1.1) (E1 ((G2, G5, E), b)).2) := rfl
  rw [← e1', ← e2', e1, ← e2]
  exact h


/-- **Grinding with the tables** (exact): the `H₂³` answers at the grinding points of the prefix
(which may depend on the `H₅` table and the cipher, not on `H₂³`) are uniform and independent of
the coins and of the tables the distinguisher reads (which do not include `H₂³`). -/
theorem joint_grind (pre : Tab5 st.params → Cipher → Bytes 16 × Bytes 16 → ByteArray)
    (D : Except String ByteArray → Vis st.params → Prop) :
    |pr (((Bytes 16 × Bytes 16) × Tab2) × Vis st.params) (fun c =>
        D (runE (recOf Hb T st w (pre c.2.2.1 c.2.2.2) c.2.1 c.1.2 c.2.2.1) T st w c.2.2.2
          (pre c.2.2.1 c.2.2.2) c.1.1) c.2) -
      pr (((Bytes 16 × Bytes 16) × Grind) × Vis st.params) (fun c =>
        D (hyb3 (recP Hb T st w c.2.1 c.2.2.1) T st w (c.1.1.2, c.1.2)
          (hiddenOutE c.2.2.2 st.params (ivOfPre Hb st c.1.1.2) (ba (deltaOf c.1.2)) c.1.1.1)) c.2)| ≤
      0 := by
  refine abs_pr_vis_le (X := fun (m : (Bytes 16 × Bytes 16) × Tab2) (v : Vis st.params) =>
      runE (recOf Hb T st w (pre v.2.1 v.2.2) v.1 m.2 v.2.1) T st w v.2.2 (pre v.2.1 v.2.2) m.1)
    (Y := fun (m : (Bytes 16 × Bytes 16) × Grind) (v : Vis st.params) =>
      hyb3 (recP Hb T st w v.1 v.2.1) T st w (m.1.2, m.2)
        (hiddenOutE v.2.2 st.params (ivOfPre Hb st m.1.2) (ba (deltaOf m.2)) m.1.1)) (fun v => ?_) D
  obtain ⟨G3, G5, E⟩ := v
  let F : (Bytes 16 × Bytes 16) × Grind → Except String ByteArray := fun m =>
    hyb3 (recP Hb T st w G3 G5) T st w (m.1.2, m.2)
      (hiddenOutE E st.params (ivOfPre Hb st m.1.2) (ba (deltaOf m.2)) m.1.1)
  have hg : Close 0 (fun c : (Bytes 16 × Bytes 16) × Tab2 => (c.1, c.2 ∘ grindKey (pre G5 E) c.1))
      (id : (Bytes 16 × Bytes 16) × Grind → _) := fun D' =>
    abs_pr_prod_sub_le _ _ fun x => close_restrict (grindKey_injective (pre G5 E) x) (fun g => D' (x, g))
  refine (hg.map F).congr (fun c => ?_) fun _ => rfl
  show runE (recOf Hb T st w (pre G5 E) G3 c.2 G5) T st w E (pre G5 E) c.1 = _
  unfold runE
  rw [recOf_realGrind, hyb3_agreeOff unread_h23 (recOf_agreeOff_h23 (pre G5 E)
    (fun _ => ByteArray.empty) G3 c.2 (fun _ => 0) G5), recOf_ivOfPre]
  rfl

/-- **H4 with the tables**: the hidden part of the commitment from a uniform root seed, with the
cipher a uniform table, against the ideal hidden part, for a distinguisher that reads the cipher
table at `q_E` keys (and the other tables freely). -/
theorem joint_h4 (hp : SmallParams st.params) (D : Except String ByteArray → Vis st.params → Prop)
    (QE : Except String ByteArray → Tab3 → Tab5 st.params → Cipher → Finset Blk)
    (hQE : ∀ o G3 G5 E E', (∀ k ∈ QE o G3 G5 E, E k = E' k) →
      (D o (G3, G5, E) ↔ D o (G3, G5, E')))
    {qE : ℕ} (hqE : ∀ o G3 G5 E, (QE o G3 G5 E).card ≤ qE) :
    |pr (((Bytes 16 × Bytes 16) × Grind) × Vis st.params) (fun c =>
        D (hyb3 (recP Hb T st w c.2.1 c.2.2.1) T st w (c.1.1.2, c.1.2)
          (hiddenOutE c.2.2.2 st.params (ivOfPre Hb st c.1.1.2) (ba (deltaOf c.1.2)) c.1.1.1)) c.2) -
      pr ((Hidden st.params × (Bytes 16 × Grind)) × Vis st.params) (fun c =>
        D (hyb3 (recP Hb T st w c.2.1 c.2.2.1) T st w c.1.2
          (hiddenIdeal (ba (deltaOf c.1.2.2)) c.1.1)) c.2)| ≤ 221 * (4607 + qE) / 2 ^ 128 := by
  let E2 : ((Bytes 16 × Grind) × (Tab3 × Tab5 st.params)) × (Blk × Cipher) ≃
      ((Bytes 16 × Bytes 16) × Grind) × Vis st.params :=
    { toFun := fun c => (((c.2.1, c.1.1.1), c.1.1.2), (c.1.2.1, (c.1.2.2, c.2.2)))
      invFun := fun c => (((c.1.1.2, c.1.2), (c.2.1, c.2.2.1)), (c.1.1.1, c.2.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let E3 : ((Bytes 16 × Grind) × (Tab3 × Tab5 st.params)) × (Hidden st.params × Cipher) ≃
      (Hidden st.params × (Bytes 16 × Grind)) × Vis st.params :=
    { toFun := fun c => ((c.2.1, c.1.1), (c.1.2.1, (c.1.2.2, c.2.2)))
      invFun := fun c => ((c.1.2, (c.2.1, c.2.2.1)), (c.1.1, c.2.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv E2, ← pr_equiv E3]
  refine abs_pr_prod_sub_le _ _ fun a => ?_
  obtain ⟨b, G3, G5⟩ := a
  let A : Hidden st.params → Cipher → Prop := fun o E =>
    D (hyb3 (recP Hb T st w G3 G5) T st w b o) (G3, G5, E)
  have h := hide_rom_query st.params (ivOfPre Hb st b.1) (ba (deltaOf b.2)) hp A
    (fun o E => QE (hyb3 (recP Hb T st w G3 G5) T st w b o) G3 G5 E)
    (fun o E E' hk => hQE _ G3 G5 E E' hk) (fun o E => hqE _ G3 G5 E)
  unfold IC.realPr IC.idealPr at h
  exact h

/-- **The deterministic steps with the tables** (exact): the unused seed slots, then the tape. -/
theorem joint_tape (D : Except String ByteArray → Vis st.params → Prop) :
    |pr ((Hidden st.params × (Bytes 16 × Grind)) × Vis st.params) (fun c =>
        D (hyb3 (recP Hb T st w c.2.1 c.2.2.1) T st w c.1.2
          (hiddenIdeal (ba (deltaOf c.1.2.2)) c.1.1)) c.2) -
      pr (IdealTape st.params × Vis st.params) (fun c =>
        D (proveIdeal (recP Hb T st w c.2.1 c.2.2.1) T st w
          (fillSib (recP Hb T st w c.2.1 c.2.2.1) T st c.1)) c.2)| ≤ 0 :=
  abs_pr_vis_le (X := fun (m : Hidden st.params × (Bytes 16 × Grind)) (v : Vis st.params) =>
      hyb3 (recP Hb T st w v.1 v.2.1) T st w m.2 (hiddenIdeal (ba (deltaOf m.2.2)) m.1))
    (Y := fun (t : IdealTape st.params) (v : Vis st.params) =>
      proveIdeal (recP Hb T st w v.1 v.2.1) T st w (fillSib (recP Hb T st w v.1 v.2.1) T st t))
    (fun v => ((hop_tail (recP Hb T st w v.1 v.2.1) T st w).trans
      (hop_tape (recP Hb T st w v.1 v.2.1) T st w)).mono (by norm_num)) D

/-- **H6 with the tables**: the sibling answers recomputed from the `H₅` table against uniform
ones, for a distinguisher that reads the `H₅` table at `q₅` keys (and the other tables freely). -/
theorem joint_h6 {cs : ByteArray → ByteArray → System GF128} (hlr : st.params.labelRows = true)
    (hzk : ZKHyp T st w cs) (D : Except String ByteArray → Vis st.params → Prop)
    (Q5 : Except String ByteArray → Tab3 → Tab5 st.params → Cipher → Finset (SKey st.params))
    (hQ5 : ∀ o G3 G5 G5' E, (∀ k ∈ Q5 o G3 G5 E, G5 k = G5' k) →
      (D o (G3, G5, E) ↔ D o (G3, G5', E)))
    {q5 : ℕ} (hq5 : ∀ o G3 G5 E, (Q5 o G3 G5 E).card ≤ q5) :
    |pr (IdealTape st.params × Vis st.params) (fun c =>
        D (proveIdeal (recP Hb T st w c.2.1 c.2.2.1) T st w
          (fillSib (recP Hb T st w c.2.1 c.2.2.1) T st c.1)) c.2) -
      pr (IdealTape st.params × Vis st.params) (fun c =>
        D (proveIdeal (recP Hb T st w c.2.1 c.2.2.1) T st w c.1) c.2)| ≤ (q5 + 1) / 2 ^ 128 := by
  let E6 : (Tab3 × Cipher) × (IdealTape st.params × Tab5 st.params) ≃
      IdealTape st.params × Vis st.params :=
    { toFun := fun c => (c.2.1, (c.1.1, (c.2.2, c.1.2)))
      invFun := fun c => ((c.2.1, c.2.2.2), (c.1, c.2.2.1))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv E6, ← pr_equiv E6]
  refine abs_pr_prod_sub_le _ _ fun a => ?_
  obtain ⟨G3, E⟩ := a
  have h := lab_rom_hyp ((Hb.withTable .h3 (seedInput (st.mu1 Hb)
      (w.extract 0 st.params.witnessBytes)) G3).withTable .h23 (gEnc fun _ => ByteArray.empty)
      fun _ => 0) T st w cs (fun o G5 => Q5 o G3 G5 E) hlr hzk (fun o G5 => D o (G3, G5, E))
    (fun o G5 G5' hk => hQ5 o G3 G5 G5' E hk) (fun o G5 => hq5 o G3 G5 E)
  simp only [← recP_eq_H5] at h
  exact h

/-- **The ideal-tape prover on a uniform tape is the simulator**, with the tables (exact). -/
theorem joint_sim {cs : ByteArray → ByteArray → System GF128} (hzk : ZKHyp T st w cs)
    (D : Except String ByteArray → Vis st.params → Prop) :
    |pr (IdealTape st.params × Vis st.params) (fun c =>
        D (proveIdeal (recP Hb T st w c.2.1 c.2.2.1) T st w c.1) c.2) -
      pr (SimCoins st.params × Vis st.params) (fun c => D (simulate st.params c.1) c.2)| ≤ 0 :=
  abs_pr_vis_le (X := fun (t : IdealTape st.params) (v : Vis st.params) =>
      proveIdeal (recP Hb T st w v.1 v.2.1) T st w t)
    (Y := fun (c : SimCoins st.params) (_ : Vis st.params) => simulate st.params c)
    (fun v => proveIdeal_close (recP Hb T st w v.1 v.2.1) T st w cs hzk) D


/-! ## The end-to-end statement -/

lemma abs_chain6 {a0 a1 a2 a3 a4 a5 a6 e1 e2 e3 e4 e5 e6 : ℝ} (h1 : |a0 - a1| ≤ e1)
    (h2 : |a1 - a2| ≤ e2) (h3 : |a2 - a3| ≤ e3) (h4 : |a3 - a4| ≤ e4) (h5 : |a4 - a5| ≤ e5)
    (h6 : |a5 - a6| ≤ e6) : |a0 - a6| ≤ e1 + e2 + e3 + e4 + e5 + e6 := by
  have := abs_sub_le a0 a1 a6
  have := abs_sub_le a1 a2 a6
  have := abs_sub_le a2 a3 a6
  have := abs_sub_le a3 a4 a6
  have := abs_sub_le a4 a5 a6
  linarith

/-- **Zero knowledge in the combined random-oracle and ideal-cipher model** (label-row layout, one
statement and witness). The hash record is `recOf Hb … pre G3 G2 G5`: the base record `Hb` with
`H₃` a uniform table `G3` on the seed inputs, `H₂³` a uniform table `G2` on the grinding points and
`H₅` a uniform table `G5` on the sibling inputs (every other domain, and these domains off those
inputs, are `Hb`'s). The BAVC's cipher is a uniform table `E` (`proveE`: the hidden part of the
commitment is computed with `E`). The tables are independent. The grinding prefix `pre G5 E` may
depend on `G5` and `E` arbitrarily (for the executable prover it is `prePrefix` with `H₅` the
table, `proveE_recOf_aes`).

A distinguisher `D` sees the proof and the tables `G3`, `G5`, `E` (not `G2`), and reads them
adaptively at `q₃`, `q₅` and `q_E` keys (`Q3`, `Q5`, `QE`: the keys may depend on the proof and on
all the tables; each condition says that `D` does not depend on the table outside them, with the
others fixed). Against the simulator `simulate` with independent uniform tables, its advantage is at
most `q₃·2⁻¹²⁸ + 0 + 221·(4607 + q_E)·2⁻¹²⁸ + (q₅ + 1)·2⁻¹²⁸` (H1, grinding, H4, H6). -/
theorem zk_rom_ic {cs : ByteArray → ByteArray → System GF128} (hlr : st.params.labelRows = true)
    (hzk : ZKHyp T st w cs) (hp : SmallParams st.params)
    (pre : Tab5 st.params → Cipher → Bytes 16 × Bytes 16 → ByteArray)
    (D : Except String ByteArray → Vis st.params → Prop)
    (Q3 : Except String ByteArray → Tab3 → Tab5 st.params → Cipher → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G5 E, (∀ k ∈ Q3 o G3 G5 E, G3 k = G3' k) →
      (D o (G3, G5, E) ↔ D o (G3', G5, E)))
    {q3 : ℕ} (hq3 : ∀ o G3 G5 E, (Q3 o G3 G5 E).card ≤ q3)
    (Q5 : Except String ByteArray → Tab3 → Tab5 st.params → Cipher → Finset (SKey st.params))
    (hQ5 : ∀ o G3 G5 G5' E, (∀ k ∈ Q5 o G3 G5 E, G5 k = G5' k) →
      (D o (G3, G5, E) ↔ D o (G3, G5', E)))
    {q5 : ℕ} (hq5 : ∀ o G3 G5 E, (Q5 o G3 G5 E).card ≤ q5)
    (QE : Except String ByteArray → Tab3 → Tab5 st.params → Cipher → Finset Blk)
    (hQE : ∀ o G3 G5 E E', (∀ k ∈ QE o G3 G5 E, E k = E' k) →
      (D o (G3, G5, E) ↔ D o (G3, G5, E')))
    {qE : ℕ} (hqE : ∀ o G3 G5 E, (QE o G3 G5 E).card ≤ qE) :
    |pr ((Bytes 16 × Tab2) × Vis st.params) (fun c =>
        D (proveE (recOf Hb T st w (pre c.2.2.1 c.2.2.2) c.2.1 c.1.2 c.2.2.1) T st w c.2.2.2
          (pre c.2.2.1 c.2.2.2) c.1.1) c.2) -
      pr (SimCoins st.params × Vis st.params) (fun c => D (simulate st.params c.1) c.2)| ≤
      q3 / 2 ^ 128 + 221 * (4607 + qE) / 2 ^ 128 + (q5 + 1) / 2 ^ 128 := by
  have h1 := joint_h1 Hb T st w pre D Q3 hQ3 hq3
  have h2 := joint_grind Hb T st w pre D
  have h3 := joint_h4 Hb T st w hp D QE hQE hqE
  have h4 := joint_tape Hb T st w D
  have h5 := joint_h6 Hb T st w hlr hzk D Q5 hQ5 hq5
  have h6 := joint_sim Hb T st w hzk D
  exact (abs_chain6 h1 h2 h3 h4 h5 h6).trans (le_of_eq (by ring))

end Chain

/-! ## The executable prover -/

section Exec

variable (Hb : Hashes) (st : Statement) (w : ByteArray)

lemma _root_.VoleMole.Verifier.Bridge.HashesWF.withTable {Hs : Hashes} (h : HashesWF Hs) (k : Kind)
    {K : Type} (enc : K → ByteArray) (G : K → Bytes k.outLen) : HashesWF (Hs.withTable k enc G) := by
  intro k' x
  simp only [Hashes.withTable]
  split_ifs with h1 h2
  · subst h1; exact size_ba _
  · subst h1; exact h _ x
  · exact h k' x

/-- **The executable grinding prefix with `H₅` the table** (the base record elsewhere; the
prefix does not read `H₃` or `H₂³`). -/
noncomputable def preReal (T : CrtTables) (G5 : Tab5 st.params) (_ : Cipher) :
    Bytes 16 × Bytes 16 → ByteArray :=
  prePrefix (Hb.withTable .h5 (sEnc Hb T st) G5) T st w

variable {Hb st w}

lemma prePrefix_recOf (T : CrtTables) (pre : Bytes 16 × Bytes 16 → ByteArray) (G3 : Tab3)
    (G2 : Tab2) (G5 : Tab5 st.params) :
    prePrefix (recOf Hb T st w pre G3 G2 G5) T st w = prePrefix (Hb.withTable .h5 (sEnc Hb T st) G5)
      T st w := by
  let X3 := Hb.withTable .h3 (seedInput (st.mu1 Hb) (w.extract 0 st.params.witnessBytes)) G3
  have a1 : (recOf Hb T st w pre G3 G2 G5).AgreeOff .h23 (X3.withTable .h5 (sEnc Hb T st) G5) := by
    unfold recOf
    exact Hashes.AgreeOff.withTable_other (k' := .h5) (X3.agreeOff_withTable .h23 (gEnc pre) G2).symm
      (by decide) (sEnc Hb T st) G5
  have a2 : (X3.withTable .h5 (sEnc Hb T st) G5).AgreeOff .h3 (Hb.withTable .h5 (sEnc Hb T st) G5) :=
    Hashes.AgreeOff.withTable_other (k' := .h5) (Hb.agreeOff_withTable .h3 _ G3).symm
      (by decide) (sEnc Hb T st) G5
  rw [prePrefix_agreeOff unread_h23 a1, prePrefix_agreeOff unread_h3 a2]

/-- **At AES and the executable prefix, `proveE` with the random-oracle record is the executable
prover** with that record (faest-arch-opt's tables, label rows). So `zk_rom_ic` with
`pre = preReal` is about the executable prover, with the BAVC's AES calls under hidden keys
replaced by the ideal cipher. -/
theorem proveE_recOf_aes {cs : ByteArray → ByteArray → System GF128}
    (hzk : ZKHyp CrtGen.tables st w cs) (hHb : HashesWF Hb) (hlr : st.params.labelRows = true)
    (G3 : Tab3) (G2 : Tab2) (G5 : Tab5 st.params) (ρ : Bytes 16) :
    proveE (recOf Hb CrtGen.tables st w (preReal Hb st w CrtGen.tables G5 aesTable) G3 G2 G5)
        CrtGen.tables st w aesTable (preReal Hb st w CrtGen.tables G5 aesTable) ρ =
      Prover.prove (recOf Hb CrtGen.tables st w (preReal Hb st w CrtGen.tables G5 aesTable) G3 G2 G5)
        CrtGen.tables st w (ba ρ) := by
  have hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows := by
    obtain ⟨h1, -, -, h2⟩ := labelRows_sizes hlr; omega
  have hR : HashesWF (recOf Hb CrtGen.tables st w (preReal Hb st w CrtGen.tables G5 aesTable) G3 G2
      G5) := by
    unfold recOf
    exact ((hHb.withTable .h3 (seedInput (st.mu1 Hb) (w.extract 0 st.params.witnessBytes)) G3).withTable
      .h23 (gEnc (preReal Hb st w CrtGen.tables G5 aesTable)) G2).withTable .h5
      (sEnc Hb CrtGen.tables st) G5
  have h : RunHyp (recOf Hb CrtGen.tables st w (preReal Hb st w CrtGen.tables G5 aesTable) G3 G2 G5)
      CrtGen.tables st w cs :=
    ⟨hzk, hR, bavcComplete, fun rho => crtComplete _ _ _ _ rho _ hlab, hlab⟩
  have hpre : prePrefix (recOf Hb CrtGen.tables st w (preReal Hb st w CrtGen.tables G5 aesTable) G3
      G2 G5) CrtGen.tables st w = preReal Hb st w CrtGen.tables G5 aesTable :=
    prePrefix_recOf _ _ _ _ _
  rw [← proveE_aes _ CrtGen.tables st w h ρ, hpre]

end Exec


end VoleMole.ZK.Sim
