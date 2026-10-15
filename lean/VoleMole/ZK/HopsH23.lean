import VoleMole.ZK.HopsJoint
import VoleMole.ZK.VerifyPre

/-!
# Zero knowledge with the `H₂³` table visible: the simulator programs it (`lean/docs/zk.md` §10.1)

`zk_rom_ic` (`ZK/HopsJoint.lean`) composes the hops in one random-oracle and ideal-cipher
experiment, but its distinguisher does not read `H₂³`. Here it does, and the simulator programs
`H₂³` at the grinding points of the prefix it recomputes from its own proof, as `simulateRO`.

**The model.** The hash record is `recH Hb … G3 G2 G5`: the base record `Hb` with `H₃` a uniform
table `G3` on the seed inputs, `H₂³` a uniform table `G2` on **every** grinding point
`pre ‖ ctr ‖ 11` with a `preLen`-byte prefix (keys `K2`: a prefix block and a counter, `enc2`), and
`H₅` a uniform table `G5` on the sibling inputs. The real world is the executable prover
`Prover.prove` with this record. The BAVC uses AES, and its hiding is the hypothesis `HideHyp`
(H4): see below for why the ideal-cipher version of H4 does not plug in here.

**(i) The programmed points are the prover's** (`hyb3_vPre`). `vPre` (`ZK/VerifyPre.lean`) is the
verifier's recomputation of `chal2 ‖ qs_check ‖ ã` from a proof. In hybrid H2 (uniform seed,
`iv_pre` and grinding answers), unless no grinding answer is accepted or the lifted `Δ'` is zero
(`GrindBad`, a function of the grinding answers only), the run returns a proof whose recomputed
prefix is the prover's grinding prefix `prePrefix` (which does not depend on the grinding answers).
The run is a real run for a record built for it (`recAt`, `prove_recAt`: `H₃` answering the seed
and `iv_pre`, `H₂³` the grinding answers at the prover's points), and the recomputation is complete
on real runs (`vPre_proveCommit`, from `verify_proveCommit`'s proof).

**(ii) The programmed answers through the hybrids.** After programming (`joint2_prog`, exact:
`pr_program_eq`) and switching the programmed points to the recomputed ones (`joint2_keys`,
`≤ Pr[GrindBad]`), the distinguisher's view is a function `Dp` of the output, the grinding answers
and the tables. Every later hop keeps the grinding answers fixed: H4 (`joint2_h4`, for every
`iv_pre` and grinding answers), the tape (`joint2_tape`: `tapeEquiv` keeps them), H6
(`joint2_h6`, from `lab_rom_hyp_s`: `lab_rom_hyp` for a distinguisher that also reads the shared
tape; the recomputation reads `H₅` only at the prover's active inputs, `vIn5_proveIdeal`, so it
adds no reads), and the simulator (`joint2_sim`, from `proveIdeal_close_shared`: the ideal-tape
proof and the simulated one are equal in law for every shared tape).

**`zk_rom_h23`.** Advantage `≤ q₃·2⁻¹²⁸ + Pr[GrindBad] + ε_bavc + (q₅ + 1)·2⁻¹²⁸` against a
distinguisher that reads `H₃` and `H₅` at `q₃`, `q₅` keys and `H₂³` freely; the simulator
programs every counter (`simTab`). **`zk_rom_h23_ro`**: the same for the simulator that programs
only `c ≤ ctr` (`simTabRO`, `simulateRO`'s points; `sim_ro_eq`: the two have the same law, by a
swap of the answers past `ctr`). `Pr[GrindBad] ≤ noHitProb + Pr[Δ' = 0]` (`grindBad_le`).

**Why AES and `HideHyp`, not the ideal cipher.** In `zk_rom_ic`'s `proveE`, the hidden part of the
commitment is computed with the cipher table `E`, but the opened subtrees, and so the verifier's
key columns, are recomputed with AES. For `E ≠ AES` the proof's recomputed prefix is then in general not
its grinding prefix (the key columns no longer satisfy `q = v + Δ·u`), so with `H₂³` visible a distinguisher that runs the
verifier's `chal3` check tells `proveE` from any programming simulator. The ideal-cipher version
needs a fully cipher-parametric prover and verifier (`BAVC.reconstruct` and the VOLE expansion
with `E`), whose reads `hide_rom_query` would then have to count.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy

/-! ## The `H₂³` table on all grinding points -/

section Table

variable (p : Params)

/-- The length of a grinding prefix `chal2 ‖ qs_check ‖ ã`: `56 + 16 + 16·(d − 1)` bytes. -/
def preLen : ℕ := 56 + 16 + 16 * (p.qsDegree - 1)

/-- The keys of the `H₂³` table: a prefix of `preLen` bytes and a counter (the grinding point
`pre ‖ ctr ‖ 11`). -/
abbrev K2 := Bytes (preLen p) × Fin nGrind

/-- The `H₂³` table. -/
abbrev Tab2G := K2 p → Bytes 16

/-- The grinding point of a key. -/
def enc2 (a : K2 p) : ByteArray := grindInput (ba a.1) a.2

lemma enc2_injective : Function.Injective (enc2 p) := by
  intro a b h
  have h2 : AES.pushLE32 (ba a.1) a.2.val.toUInt32 = AES.pushLE32 (ba b.1) b.2.val.toUInt32 :=
    push_injective 11 h
  have h1' : a.1 = b.1 := by
    funext i
    have := congrArg (fun x : ByteArray => x.get! i) h2
    simpa only [get!_pushLE32, size_ba, i.isLt, ↓reduceIte, get!_ba _ i.isLt] using this
  refine Prod.ext h1' ?_
  have h3 : grindInput (ba a.1) a.2 = grindInput (ba a.1) b.2 := by
    have : enc2 p a = enc2 p b := h
    simp only [enc2, h1'] at this ⊢
    exact this
  exact grindInput_injective _ h3

/-- The key of the grinding point of counter `c` for the prefix `pre`. -/
def key2 (pre : ByteArray) (c : Fin nGrind) : K2 p := (blk (preLen p) pre, c)

lemma key2_injective (pre : ByteArray) : Function.Injective (key2 p pre) :=
  fun _ _ h => (Prod.ext_iff.1 h).2

lemma enc2_key2 {pre : ByteArray} (h : pre.size = preLen p) (c : Fin nGrind) :
    enc2 p (key2 p pre c) = grindInput pre c := by
  simp only [enc2, key2, ba_blk_of_size h]

/-- With `H₂³` the table on the grinding points, a prefix of the right length gets the table's
answers at its keys. -/
lemma realGrind_withTable2 (Hs : Hashes) (G : Tab2G p) {pre : ByteArray} (h : pre.size = preLen p) :
    realGrind (Hs.withTable .h23 (enc2 p) G) pre = G ∘ key2 p pre := by
  funext c
  simp only [realGrind, Function.comp_apply]
  rw [show (AES.pushLE32 pre c.val.toUInt32).push 11 = enc2 p (key2 p pre c) from
    (enc2_key2 p h c).symm, Hashes.withTable_enc Hs .h23 (enc2 p) G (key2 p pre c),
    keyOf_eq (enc2_injective p)]
  exact blk_ba _

end Table

/-! ## `vPre` reads neither `H₃` nor `H₂³`, and `H₅` only at the verifier's gate inputs -/

section VPreCongr

lemma vPre_agreeOff {k : Kind} {Hs Hs' : Hashes} (hu : Unread k) (h : Hs.AgreeOff k Hs')
    (T : CrtTables) (st : Statement) : vPre Hs T st = vPre Hs' T st := by
  funext proof
  simp only [vPre, vPreP, vPreOf, ivOf, crtReconstruct, h.mu1' hu st, h .h4 (Ne.symm hu.2.2.1),
    h .h1 (Ne.symm hu.2.2.2.1), h.chal1 hu.2.2.2.2.1, h .h5 (Ne.symm hu.2.2.2.2.2.2.1),
    h.chal2 hu.2.2.2.2.2.1, h.muDelayed hu.1 st, h.combBytes hu.2.2.2.2.2.2.2 st]

/-- **The verifier's `H₅` inputs**: the gate inputs `gateInputs` at its key columns (none if the
opening is malformed). -/
def vIn5 (Hs : Hashes) (T : CrtTables) (st : Statement) (proof : ByteArray) : List ByteArray :=
  let pf : Proof := { params := st.params, bytes := proof }
  match BAVC.reconstruct (ivOf Hs pf (st.mu1 Hs)) pf.opening pf.delta with
  | none => []
  | some leaves => gateInputs st.params T (ivOf Hs pf (st.mu1 Hs))
      (convertToVole pf (ivOf Hs pf (st.mu1 Hs)) leaves)

lemma vIn5_length_le (Hs : Hashes) (T : CrtTables) (st : Statement) (proof : ByteArray) :
    (vIn5 Hs T st proof).length ≤ st.params.nMult := by
  unfold vIn5
  dsimp only
  split
  · simp
  · simp [gateInputs]

/-- **`vPre` reads `H₅` only at `vIn5`**: two records that agree off `H₅`, and on `H₅` at the
verifier's gate inputs, recompute the same prefix. -/
theorem vPre_h5_congr {Hs Hs' : Hashes} (h : Hs.AgreeOff .h5 Hs') (T : CrtTables) (st : Statement)
    (proof : ByteArray) (h5 : ∀ x ∈ vIn5 Hs T st proof, Hs.hash .h5 x = Hs'.hash .h5 x) :
    vPre Hs T st proof = vPre Hs' T st proof := by
  have hmu := h.mu1 (by decide) (by decide) st
  have h4 := h .h4 (by decide)
  have h1 := h .h1 (by decide)
  unfold vIn5 at h5
  simp only [vPre, vPreP, ivOf, hmu, h4] at h5 ⊢
  split
  · rfl
  · rename_i leaves hl
    rw [hl] at h5
    simp only [vPreOf, ivOf, crtReconstruct, crtReconstructAt, gateHashes, hmu, h4, h1,
      h.chal1 (by decide), h.chal2 (by decide), h.muDelayed (by decide) st,
      h.combBytes (fun _ => nofun) st, List.map_congr_left h5]

end VPreCongr

/-! ## The record -/

section Rec

variable (Hb : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)

/-- **The hash record of the random-oracle model with `H₂³` visible**: the base record `Hb` with
`H₃` answered by `G3` at the seed inputs, `H₂³` by `G2` at **every** grinding point
`pre ‖ ctr ‖ 11` with a prefix of `preLen` bytes (`enc2`), and `H₅` by `G5` at the sibling inputs
(`Hb` elsewhere). -/
noncomputable def recH (G3 : Tab3) (G2 : Tab2G st.params) (G5 : Tab5 st.params) : Hashes :=
  ((Hb.withTable .h3 (seedInput (st.mu1 Hb) (w.extract 0 st.params.witnessBytes)) G3).withTable
    .h23 (enc2 st.params) G2).withTable .h5 (sEnc Hb T st) G5

/-- The base record with the `H₅` table only: the record the simulator recomputes the grinding
prefix with, and the prover's prefix is computed with. -/
noncomputable def rec5 (G5 : Tab5 st.params) : Hashes := Hb.withTable .h5 (sEnc Hb T st) G5

/-- The record once the `H₂³` table is no longer read. -/
noncomputable def recB (G3 : Tab3) (G5 : Tab5 st.params) : Hashes := recH Hb T st w G3 (fun _ => 0) G5

/-- **The prover's grinding prefix** with the `H₅` table (it reads neither `H₃` nor `H₂³`). -/
noncomputable def preR (G5 : Tab5 st.params) : Bytes 16 × Bytes 16 → ByteArray :=
  prePrefix (rec5 Hb T st G5) T st w

variable {Hb T st w}

lemma recH_hash_ne {G3 : Tab3} {G2 : Tab2G st.params} {G5 : Tab5 st.params} {k : Kind}
    (h3 : k ≠ .h3) (h23 : k ≠ .h23) (h5 : k ≠ .h5) :
    (recH Hb T st w G3 G2 G5).hash k = Hb.hash k := by
  funext x
  simp only [recH, Hashes.withTable, h3, h23, h5, ite_false]

lemma recH_mu1 (G3 : Tab3) (G2 : Tab2G st.params) (G5 : Tab5 st.params) :
    st.mu1 (recH Hb T st w G3 G2 G5) = st.mu1 Hb := by
  simp only [Statement.mu1, mu, recH_hash_ne (k := .mu) (by decide) (by decide) (by decide),
    recH_hash_ne (k := .muDelayed) (by decide) (by decide) (by decide)]

lemma recH_agreeOff_h3 (G3 G3' : Tab3) (G2 : Tab2G st.params) (G5 : Tab5 st.params) :
    (recH Hb T st w G3 G2 G5).AgreeOff .h3 (recH Hb T st w G3' G2 G5) := by
  intro k hk
  funext x
  by_cases h5 : k = .h5
  · subst h5; simp only [recH, Hashes.withTable, reduceCtorEq, ite_true, ite_false]
  by_cases h23 : k = .h23
  · subst h23; simp only [recH, Hashes.withTable, reduceCtorEq, ite_true, ite_false]
  · simp only [recH, Hashes.withTable, h5, h23, hk, ite_false]

lemma recH_agreeOff_h23 (G3 : Tab3) (G2 G2' : Tab2G st.params) (G5 : Tab5 st.params) :
    (recH Hb T st w G3 G2 G5).AgreeOff .h23 (recH Hb T st w G3 G2' G5) := by
  intro k hk
  funext x
  by_cases h5 : k = .h5
  · subst h5; simp only [recH, Hashes.withTable, reduceCtorEq, ite_true, ite_false]
  by_cases h3 : k = .h3
  · subst h3; simp only [recH, Hashes.withTable, reduceCtorEq, ite_true, ite_false]
  · simp only [recH, Hashes.withTable, h5, h3, hk, ite_false]

/-- `recH` agrees with `rec5` off `H₃` and `H₂³`, in two steps. -/
lemma recH_rec5 (G3 : Tab3) (G2 : Tab2G st.params) (G5 : Tab5 st.params) :
    (recH Hb T st w G3 G2 G5).AgreeOff .h23
      ((Hb.withTable .h3 (seedInput (st.mu1 Hb) (w.extract 0 st.params.witnessBytes)) G3).withTable
        .h5 (sEnc Hb T st) G5) ∧
    ((Hb.withTable .h3 (seedInput (st.mu1 Hb) (w.extract 0 st.params.witnessBytes)) G3).withTable
        .h5 (sEnc Hb T st) G5).AgreeOff .h3 (rec5 Hb T st G5) := by
  let X3 := Hb.withTable .h3 (seedInput (st.mu1 Hb) (w.extract 0 st.params.witnessBytes)) G3
  refine ⟨?_, ?_⟩
  · unfold recH
    exact Hashes.AgreeOff.withTable_other (k' := .h5)
      (X3.agreeOff_withTable .h23 (enc2 st.params) G2).symm (by decide) (sEnc Hb T st) G5
  · exact Hashes.AgreeOff.withTable_other (k' := .h5) (Hb.agreeOff_withTable .h3 _ G3).symm
      (by decide) (sEnc Hb T st) G5

lemma prePrefix_recH (G3 : Tab3) (G2 : Tab2G st.params) (G5 : Tab5 st.params) :
    prePrefix (recH Hb T st w G3 G2 G5) T st w = preR Hb T st w G5 := by
  obtain ⟨a1, a2⟩ := recH_rec5 (w := w) G3 G2 G5
  rw [prePrefix_agreeOff unread_h23 a1, prePrefix_agreeOff unread_h3 a2, preR]

lemma vPre_recH (G3 : Tab3) (G2 : Tab2G st.params) (G5 : Tab5 st.params) :
    vPre (recH Hb T st w G3 G2 G5) T st = vPre (rec5 Hb T st G5) T st := by
  obtain ⟨a1, a2⟩ := recH_rec5 (w := w) G3 G2 G5
  rw [vPre_agreeOff unread_h23 a1, vPre_agreeOff unread_h3 a2]

lemma recH_ivOfPre (G3 : Tab3) (G2 : Tab2G st.params) (G5 : Tab5 st.params) :
    ivOfPre (recH Hb T st w G3 G2 G5) st = ivOfPre Hb st := by
  funext a
  simp only [ivOfPre, recH_mu1, recH_hash_ne (k := .h4) (by decide) (by decide) (by decide)]

/-- With the record's `H₃` table, the seed and `iv_pre` of `rho` are the table's answer. -/
lemma recH_h3Seed (G3 : Tab3) (G2 : Tab2G st.params) (G5 : Tab5 st.params) (ρ : Bytes 16) :
    h3Seed (recH Hb T st w G3 G2 G5) (st.mu1 (recH Hb T st w G3 G2 G5))
      (w.extract 0 st.params.witnessBytes) (ba ρ) = splitSeed (G3 ρ) := by
  rw [recH_mu1, h3Seed_congr (Hs' := Hb.withTable .h3 (seedInput (st.mu1 Hb)
    (w.extract 0 st.params.witnessBytes)) G3), h3Seed_withTable]
  funext x
  simp only [recH, Hashes.withTable, reduceCtorEq, ite_false]

/-- With the record's `H₂³` table, the grinding answers at a prefix of `preLen` bytes are the
table's. -/
lemma recH_realGrind (G3 : Tab3) (G2 : Tab2G st.params) (G5 : Tab5 st.params) {pre : ByteArray}
    (hpre : pre.size = preLen st.params) :
    realGrind (recH Hb T st w G3 G2 G5) pre = G2 ∘ key2 st.params pre := by
  rw [realGrind_congr (Hs' := (Hb.withTable .h3 (seedInput (st.mu1 Hb)
    (w.extract 0 st.params.witnessBytes)) G3).withTable .h23 (enc2 st.params) G2),
    realGrind_withTable2 st.params _ G2 hpre]
  funext y
  simp only [recH, Hashes.withTable, reduceCtorEq, ite_false]

lemma recH_wf (hHb : HashesWF Hb) (G3 : Tab3) (G2 : Tab2G st.params) (G5 : Tab5 st.params) :
    HashesWF (recH Hb T st w G3 G2 G5) :=
  ((hHb.withTable .h3 _ G3).withTable .h23 _ G2).withTable .h5 _ G5

/-- `recB` is the `H₅` table on top of a record (`HopsH6.H5`), for `lab_rom_hyp`. -/
lemma recB_eq_H5 (G3 : Tab3) (G5 : Tab5 st.params) :
    recB Hb T st w G3 G5 = H5 ((Hb.withTable .h3 (seedInput (st.mu1 Hb)
      (w.extract 0 st.params.witnessBytes)) G3).withTable .h23 (enc2 st.params)
      fun _ => 0) T st G5 := by
  have h1 := Hb.agreeOff_withTable .h3 (seedInput (st.mu1 Hb) (w.extract 0 st.params.witnessBytes)) G3
  have h2 := (Hb.withTable .h3 (seedInput (st.mu1 Hb) (w.extract 0 st.params.witnessBytes)) G3
    ).agreeOff_withTable .h23 (enc2 st.params) (fun _ => 0)
  rw [recB, recH, H5, sEnc_agreeOff unread_h3 h1, sEnc_agreeOff unread_h23 h2]
  rfl

end Rec

/-! ## The verifier recomputes the prover's grinding prefix, at every grinding outcome -/

section Link

lemma gfToBytes_size' (a : GF128) : (gfToBytes a).size = 16 := by
  show (W128.pushWord (W128.pushWord ByteArray.empty a.lo) a.hi).size = 16
  rw [ByteArray.size, pushWord_data, Array.size_append, ByteArray.size_data, ← ByteArray.size,
    ByteArray.size, pushWord_data, Array.size_append]
  simp [ByteArray.size, leBytes_length]

variable (Hs : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)

/-- **The prover's grinding prefix has `preLen` bytes** (QuickSilver succeeds for a satisfying
witness). -/
theorem prePrefix_size (hHs : HashesWF Hs) {cs : ByteArray → ByteArray → System GF128}
    (h : ZKHypQ st w cs) (x : Bytes 16 × Bytes 16) :
    (prePrefix Hs T st w x).size = preLen st.params := by
  unfold prePrefix
  set s := pendAt Hs T st (w.extract 0 st.params.witnessBytes) x
  have h0 : ∀ i, gfOfBytes (Proof.mk st.params (Prover.assemble st.params
      (realF1 st.params s w))).qsProof (16 * i) = 0 := by
    intro i
    rw [(fields_assemble st.params _).2.2.2.2.1]
    show gfOfBytes (Prover.fit s.fields.qsProof _) _ = 0
    rw [show s.fields.qsProof = ByteArray.empty from rfl, fit_empty, gfOfBytes_zeros]
  have hq := qsProve_eq (Proof.mk st.params (Prover.assemble st.params (realF1 st.params s w)))
    (realC2 Hs st s w) (st.values s.chal1 (st.combBytes Hs (realC2 Hs st s w))) s.vRows s.vMask
    s.uMask w (cs s.chal1 (st.combBytes Hs (realC2 Hs st s w))) (h.hvals _ _) (h.hdeg _ _) h.hd
    h.hd' h0 h.hI (h.hsat _ _)
  rw [realPre, hq]
  simp only [ByteArray.size_append, gfsToBytes_size, Array.size_map, Array.size_range,
    gfToBytes_size', preLen]
  rw [realC2, chal2, hHs]
  rfl

/-- **The bad grinding outcomes**: no accepted answer, or a zero lifted `Δ'` (the verifier then
stops before `qs_check`). A function of the grinding answers only. -/
def GrindBad (T : CrtTables) (g : Grind) : Prop := firstHit g = none ∨ tDL T (deltaOf g) = 0

/-- The `H₃` input of the empty `rho`. -/
def seed0 : ByteArray := (w.extract 0 st.params.witnessBytes ++ st.mu1 Hs ++ ByteArray.empty).push 3

/-- **The run of hybrid H2 at any seed, `iv_pre` and grinding answers is a real run** of the
executable prover, for a record that answers `H₃` at the seed input of the empty `rho` with the
seed and `iv_pre`, and `H₂³` at the grinding points of the prover's prefix with the answers. -/
noncomputable def recAt (x : Bytes 16 × Bytes 16) (g : Grind) : Hashes :=
  (Hs.withTable .h23 (grindInput (prePrefix Hs T st w x)) g).withTable .h3
    (fun _ : Unit => seed0 Hs st w) (fun _ => joinSeed x)

variable {Hs T st w}

lemma recAt_agree (x : Bytes 16 × Bytes 16) (g : Grind) :
    Hs.AgreeOff .h23 (Hs.withTable .h23 (grindInput (prePrefix Hs T st w x)) g) ∧
    (Hs.withTable .h23 (grindInput (prePrefix Hs T st w x)) g).AgreeOff .h3 (recAt Hs T st w x g) :=
  ⟨Hs.agreeOff_withTable .h23 _ g, Hashes.agreeOff_withTable _ .h3 _ _⟩

lemma recAt_mu1 (x : Bytes 16 × Bytes 16) (g : Grind) :
    st.mu1 (recAt Hs T st w x g) = st.mu1 Hs :=
  (((recAt_agree x g).1.mu1' unread_h23 st).trans ((recAt_agree x g).2.mu1' unread_h3 st)).symm

lemma recAt_prePrefix (x : Bytes 16 × Bytes 16) (g : Grind) :
    prePrefix (recAt Hs T st w x g) T st w = prePrefix Hs T st w :=
  ((prePrefix_agreeOff unread_h23 (recAt_agree x g).1 T st w).trans
    (prePrefix_agreeOff unread_h3 (recAt_agree x g).2 T st w)).symm

lemma recAt_pendAt (x : Bytes 16 × Bytes 16) (g : Grind) (wP : ByteArray) (y : Bytes 16 × Bytes 16) :
    pendAt (recAt Hs T st w x g) T st wP y = pendAt Hs T st wP y :=
  ((pendAt_agreeOff unread_h23 (recAt_agree x g).1 T st wP y).trans
    (pendAt_agreeOff unread_h3 (recAt_agree x g).2 T st wP y)).symm

lemma recAt_vPre (x : Bytes 16 × Bytes 16) (g : Grind) :
    vPre (recAt Hs T st w x g) T st = vPre Hs T st :=
  ((vPre_agreeOff unread_h23 (recAt_agree x g).1 T st).trans
    (vPre_agreeOff unread_h3 (recAt_agree x g).2 T st)).symm

lemma recAt_wf (hHs : HashesWF Hs) (x : Bytes 16 × Bytes 16) (g : Grind) :
    HashesWF (recAt Hs T st w x g) :=
  (hHs.withTable .h23 _ g).withTable .h3 _ _

lemma recAt_h3Seed (x : Bytes 16 × Bytes 16) (g : Grind) :
    h3Seed (recAt Hs T st w x g) (st.mu1 (recAt Hs T st w x g))
      (w.extract 0 st.params.witnessBytes) ByteArray.empty = x := by
  rw [recAt_mu1]
  have e := Hashes.withTable_enc (Hs.withTable .h23 (grindInput (prePrefix Hs T st w x)) g) .h3
    (fun _ : Unit => seed0 Hs st w) (fun _ => joinSeed x) ()
  unfold h3Seed
  rw [show (w.extract 0 st.params.witnessBytes ++ st.mu1 Hs ++ ByteArray.empty).push 3 =
    seed0 Hs st w from rfl]
  rw [show (recAt Hs T st w x g).hash .h3 (seed0 Hs st w) = ba (joinSeed x) from e]
  exact splitSeed_joinSeed x

lemma recAt_realGrind (x : Bytes 16 × Bytes 16) (g : Grind) :
    realGrind (recAt Hs T st w x g) (prePrefix Hs T st w x) = g := by
  funext c
  simp only [realGrind]
  rw [show (recAt Hs T st w x g).hash .h23 =
      (Hs.withTable .h23 (grindInput (prePrefix Hs T st w x)) g).hash .h23 from
      ((recAt_agree x g).2 .h23 (by decide)).symm,
    show (AES.pushLE32 (prePrefix Hs T st w x) c.val.toUInt32).push 11 =
      grindInput (prePrefix Hs T st w x) c from rfl,
    Hashes.withTable_enc Hs .h23 (grindInput _) g c, keyOf_eq (grindInput_injective _)]
  exact blk_ba _

theorem prove_recAt (hHs : HashesWF Hs) {cs : ByteArray → ByteArray → System GF128}
    (h : ZKHyp CrtGen.tables st w cs)
    (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    (x : Bytes 16 × Bytes 16) (g : Grind) :
    Prover.prove (recAt Hs CrtGen.tables st w x g) CrtGen.tables st w ByteArray.empty =
      hyb2 Hs CrtGen.tables st w (x.1, x.2, g) := by
  set T := CrtGen.tables
  set wP := w.extract 0 st.params.witnessBytes
  set R2 := recAt Hs T st w x g
  have hR2 : HashesWF R2 := recAt_wf hHs x g
  have h5 : R2.hash .h5 = Hs.hash .h5 :=
    (((recAt_agree x g).1 .h5 (by decide)).trans ((recAt_agree x g).2 .h5 (by decide))).symm
  have htape : ∀ s g', tapeAt R2 T st.params s g' = tapeAt Hs T st.params s g' := by
    intro s g'; simp only [tapeAt, realPads, sibAnswers, h5]
  have hpi : proveIdeal R2 T st w = proveIdeal Hs T st w :=
    ((proveIdeal_agreeOff unread_h23 (recAt_agree x g).1 T st w).trans
      (proveIdeal_agreeOff unread_h3 (recAt_agree x g).2 T st w)).symm
  rw [prove_eq_proveIdeal R2 T st w ByteArray.empty cs h.q hR2 bavcComplete
    (crtComplete R2 st.params _ _ _ _ hlab) hlab, tapeOf_eq_tape1 R2 T st w hR2, recAt_h3Seed,
    show realPre R2 st (pendAt R2 T st wP x) w = prePrefix Hs T st w x by
      rw [← recAt_prePrefix x g]; rfl,
    recAt_realGrind, recAt_pendAt, htape, hpi]
  rfl

/-- **(i) The verifier recomputes the prover's grinding prefix, in hybrid H2** (uniform seed,
`iv_pre` and grinding answers): unless the grinding outcome is bad (`GrindBad`), the run returns a
proof, and the prefix `vPre` recomputed from it is the prover's prefix `prePrefix` of the seed and
`iv_pre` (which does not depend on the grinding answers). -/
theorem hyb3_vPre (hHs : HashesWF Hs) {cs : ByteArray → ByteArray → System GF128}
    (h : ZKHyp CrtGen.tables st w cs)
    (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    (x : Bytes 16 × Bytes 16) (g : Grind) (hg : ¬ GrindBad CrtGen.tables g) :
    ∃ proof, hyb3 Hs CrtGen.tables st w (x.2, g)
        (hiddenOut st.params (ivOfPre Hs st x.2) (ba (deltaOf g)) x.1) = .ok proof ∧
      vPre Hs CrtGen.tables st proof = prePrefix Hs CrtGen.tables st w x := by
  set T := CrtGen.tables
  set wP := w.extract 0 st.params.witnessBytes
  have e1 : hyb2 Hs T st w (x.1, x.2, g) = hyb3 Hs T st w (x.2, g)
      (hiddenOut st.params (ivOfPre Hs st x.2) (ba (deltaOf g)) x.1) := by
    rw [hyb2, ← real_fillSib Hs T st w hHs bavcComplete hlab (pendAt Hs T st wP (x.1, x.2)) rfl
      (size_ba _) (size_ba _), fillSib_tapeAt Hs T st wP x.1 x.2 g, pendAt_iv]
    rfl
  rw [← e1]
  obtain ⟨hnone, hΔ⟩ := not_or.1 hg
  obtain ⟨⟨ctr, δ⟩, hf⟩ := Option.ne_none_iff_exists'.1 hnone
  have hd : deltaOf g = δ := by unfold deltaOf; rw [hf]; rfl
  set t := tapeAt Hs T st.params (pendAt Hs T st wP (x.1, x.2)) g with ht
  have hok : hyb2 Hs T st w (x.1, x.2, g) = .ok (simAssemble st.params t.1 ctr δ
      (fieldsOf Hs T st w cs t.1 (hitOf t.1).1 (hitOf t.1).2 t.2).1) := by
    show proveIdeal Hs T st w (t.1, t.2) = _
    rw [proveIdeal_eq_outOf T st w cs Hs h t.1 t.2]
    unfold outOf
    rw [show t.1.2.1 = g from rfl, hf]
  refine ⟨_, hok, ?_⟩
  set prf := simAssemble st.params t.1 ctr δ
    (fieldsOf Hs T st w cs t.1 (hitOf t.1).1 (hitOf t.1).2 t.2).1 with hprf
  have hp := prove_recAt hHs h hlab x g
  rw [hok] at hp
  have hw : wP ++ w.extract st.params.witnessBytes w.size = w := by
    have hpre : wP = w := by
      show w.extract 0 st.params.witnessBytes = w
      rw [← h.hw, ByteArray.extract_zero_size]
    have hsuf : w.extract st.params.witnessBytes w.size = ByteArray.empty := by
      rw [h.hw, ByteArray.extract_eq_empty_iff]; omega
    rw [hpre, hsuf, ByteArray.append_empty]
  have hdel : ({ params := st.params, bytes := prf } : Proof).delta = ba δ := by
    rw [hprf, simAssemble, (fields_assemble st.params _).2.2.2.2.2.2.1]
    exact fit_of_size (size_ba _)
  have hΔ' : (W128.rowMul (BAVC.deltaBit ({ params := st.params, bytes := prf } : Proof).delta) 120
      T.wCrt).toGF ≠ 0 := by
    rw [hdel]; rw [hd] at hΔ; exact hΔ
  have hv := vPre_proveCommit (recAt Hs T st w x g) (recAt_wf hHs x g) bavcComplete T st _ wP
    ByteArray.empty st.binder1 (w.extract st.params.witnessBytes w.size) _ rfl rfl hp
    (crtComplete _ st.params _ _ _ _ hlab) hΔ' cs h.hvals h.hdeg h.hd h.hd'
  rw [recAt_vPre, hw, voleGen_eq_pendAt _ (recAt_wf hHs x g), recAt_h3Seed,
    show realPre (recAt Hs T st w x g) st (pendAt (recAt Hs T st w x g) T st wP x) w =
      prePrefix (recAt Hs T st w x g) T st w x from rfl, recAt_prePrefix] at hv
  exact hv

end Link

/-! ## H6 and the simulator, for distinguishers that also see the grinding answers -/

section Shared

variable (Hs : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)
  (cs : ByteArray → ByteArray → System GF128)

/-- **H6 in the ROM, for a distinguisher that also reads the shared tape** (`lab_rom_query` with
`D` and its `H₅` reads depending on the shared part of the tape, which carries the grinding
answers). The read condition is stated on the run itself: two tables that agree on the prover's
reads and on `QD` give the same verdict. -/
theorem lab_rom_query_s (hlr : st.params.labelRows = true) (h : ZKHyp T st w cs)
    (D : Except String ByteArray → Shared → (SKey st.params → Bytes 4) → Prop)
    (QD : Except String ByteArray → Shared → (SKey st.params → Bytes 4) → Finset (SKey st.params))
    (hA : ∀ (t : IdealTape st.params) G G', (∀ k ∈ proverKeys Hs T st t ∪
        QD (proveIdeal (H5 Hs T st G) T st w t) t.1 G, G k = G' k) →
      (D (proveIdeal (H5 Hs T st G) T st w t) t.1 G ↔ D (proveIdeal (H5 Hs T st G') T st w t) t.1 G'))
    {q : ℕ} (hq : ∀ o s G, (QD o s G).card ≤ q) :
    |pr ((Shared × PadsU st.params) × (SKey st.params → Bytes 4)) (fun x =>
        D (proveIdeal (H5 Hs T st x.2) T st w (fillSib (H5 Hs T st x.2) T st
          (x.1.1, withSib x.1.2 fun _ => fun _ => 0))) x.1.1 x.2) -
      pr ((Shared × PadsU st.params) × ((SKey st.params → Bytes 4) × Sib))
        (fun x => D (proveIdeal (H5 Hs T st x.2.1) T st w (x.1.1, withSib x.1.2 x.2.2)) x.1.1
          x.2.1)| ≤
      (q + 1) / 2 ^ 128 := by
  refine (lab_rom Hs T st (fun t G => D (proveIdeal (H5 Hs T st G) T st w t) t.1 G)
    (fun t G => proverKeys Hs T st t ∪ QD (proveIdeal (H5 Hs T st G) T st w t) t.1 G)
    fun t G G' hG => hA t G G' hG).trans ?_
  let E : (SKey st.params → Bytes 4) × IdealTape st.params ≃
      (Shared × PadsU st.params) × ((SKey st.params → Bytes 4) × Sib) :=
    { toFun := fun y => ((y.2.1, dropSib y.2.2), (y.1, y.2.2.2.2.2.2.2.2))
      invFun := fun x => (x.2.1, (x.1.1, withSib x.1.2 x.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv E]
  refine pr_prod_le _ fun G => pr_prod_le _ fun s => ?_
  exact pr_bad_le Hs T st w cs (fun o G => QD o s G) hlr h (fun o G => hq o s G) G s

/-- **`LabHyp` in the ROM, for a distinguisher that also reads the shared tape.** -/
theorem lab_rom_hyp_s (hlr : st.params.labelRows = true) (h : ZKHyp T st w cs)
    (D : Except String ByteArray → Shared → (SKey st.params → Bytes 4) → Prop)
    (QD : Except String ByteArray → Shared → (SKey st.params → Bytes 4) → Finset (SKey st.params))
    (hA : ∀ (t : IdealTape st.params) G G', (∀ k ∈ proverKeys Hs T st t ∪
        QD (proveIdeal (H5 Hs T st G) T st w t) t.1 G, G k = G' k) →
      (D (proveIdeal (H5 Hs T st G) T st w t) t.1 G ↔ D (proveIdeal (H5 Hs T st G') T st w t) t.1 G'))
    {q : ℕ} (hq : ∀ o s G, (QD o s G).card ≤ q) :
    |pr (IdealTape st.params × (SKey st.params → Bytes 4)) (fun x =>
        D (proveIdeal (H5 Hs T st x.2) T st w (fillSib (H5 Hs T st x.2) T st x.1)) x.1.1 x.2) -
      pr (IdealTape st.params × (SKey st.params → Bytes 4))
        (fun x => D (proveIdeal (H5 Hs T st x.2) T st w x.1) x.1.1 x.2)| ≤ (q + 1) / 2 ^ 128 := by
  let E2 : ((Shared × PadsU st.params) × (SKey st.params → Bytes 4)) × Sib ≃
      IdealTape st.params × (SKey st.params → Bytes 4) :=
    { toFun := fun y => ((y.1.1.1, withSib y.1.1.2 y.2), y.1.2)
      invFun := fun x => (((x.1.1, dropSib x.1.2), x.2), x.1.2.2.2.2.2.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let E3 : (Shared × PadsU st.params) × ((SKey st.params → Bytes 4) × Sib) ≃
      IdealTape st.params × (SKey st.params → Bytes 4) :=
    { toFun := fun y => ((y.1.1, withSib y.1.2 y.2.2), y.2.1)
      invFun := fun x => ((x.1.1, dropSib x.1.2), (x.2, x.1.2.2.2.2.2.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have e1 : pr (IdealTape st.params × (SKey st.params → Bytes 4)) (fun x =>
      D (proveIdeal (H5 Hs T st x.2) T st w (fillSib (H5 Hs T st x.2) T st x.1)) x.1.1 x.2) =
      pr ((Shared × PadsU st.params) × (SKey st.params → Bytes 4)) (fun x =>
        D (proveIdeal (H5 Hs T st x.2) T st w (fillSib (H5 Hs T st x.2) T st
          (x.1.1, withSib x.1.2 fun _ => fun _ => 0))) x.1.1 x.2) := by
    rw [← pr_equiv E2, ← pr_prod_fst (β := Sib) (fun x : (Shared × PadsU st.params) ×
      (SKey st.params → Bytes 4) => D (proveIdeal (H5 Hs T st x.2) T st w (fillSib (H5 Hs T st x.2)
        T st (x.1.1, withSib x.1.2 fun _ => fun _ => 0))) x.1.1 x.2)]
    refine pr_congr fun y => ?_
    show D (proveIdeal (H5 Hs T st y.1.2) T st w (fillSib (H5 Hs T st y.1.2) T st
        (y.1.1.1, withSib y.1.1.2 y.2))) y.1.1.1 y.1.2 ↔ _
    rw [fillSib_withSib T st _ y.1.1.1 y.1.1.2 y.2 fun _ => fun _ => 0]
  have e2 : pr (IdealTape st.params × (SKey st.params → Bytes 4))
      (fun x => D (proveIdeal (H5 Hs T st x.2) T st w x.1) x.1.1 x.2) =
      pr ((Shared × PadsU st.params) × ((SKey st.params → Bytes 4) × Sib))
        (fun x => D (proveIdeal (H5 Hs T st x.2.1) T st w (x.1.1, withSib x.1.2 x.2.2)) x.1.1
          x.2.1) :=
    (pr_equiv E3 _).symm
  rw [e1, e2]
  exact lab_rom_query_s Hs T st w cs hlr h D QD hA hq

lemma simulate_eq_outOf (s : Shared) (f : SimFields st.params) :
    simulate st.params (s, f) = outOf st s f := by
  rcases hf : firstHit s.2.1 with _ | ⟨ctr, d⟩
  · simp only [simulate, outOf, hf]
  · simp only [simulate, outOf, simAssemble, hf]

/-- **The ideal-tape prover and the simulator, with the shared tape** (exact): for every shared
tape (which carries the grinding answers), the ideal-tape proof on uniform pads is distributed as
the simulated proof on uniform fields. -/
theorem proveIdeal_close_shared (h : ZKHyp T st w cs) :
    Close 0 (fun t : IdealTape st.params => (proveIdeal Hs T st w t, t.1))
      (fun c : SimCoins st.params => (simulate st.params c, c.1)) := by
  have hs : ∀ s : Shared, Close 0 (fun t : Pads st.params => (proveIdeal Hs T st w (s, t), s))
      (fun f : SimFields st.params => (simulate st.params (s, f), s)) := by
    intro s
    have h1 := (upush_fieldsOf Hs T st w cs s (hitOf s).1 (hitOf s).2 h.hT h.hnm).close
      fun y : SimFields st.params × Bytes (labelBytes st.params) => (outOf st s y.1, s)
    have h2 : Close 0 (fun y : SimFields st.params × Bytes (labelBytes st.params) =>
        (outOf st s y.1, s)) (fun f : SimFields st.params => (outOf st s f, s)) :=
      close_prod_fst (X := fun f : SimFields st.params => (outOf st s f, s))
    exact ((h1.trans h2).mono (by norm_num)).congr
      (fun t => by rw [proveIdeal_eq_outOf T st w cs Hs h s t])
      fun f => by rw [simulate_eq_outOf]
  exact Close.prod_right (X := fun s (t : Pads st.params) => (proveIdeal Hs T st w (s, t), s))
    (Y := fun s (f : SimFields st.params) => (simulate st.params (s, f), s)) hs

end Shared

/-! ## The verifier's `H₅` inputs on an ideal-tape proof are the prover's -/

section Reads

variable (Hs : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)

/-- **On a proof assembled from a shared tape, the verifier hashes the active gate inputs**: the
gate inputs at the key columns of the tape's opening, `Δ` and corrections. -/
theorem vIn5_simAssemble (s : Shared) (ctr : ℕ) (δ : Bytes 16) (f : SimFields st.params)
    (hf : firstHit s.2.1 = some (ctr, δ)) :
    ∀ x ∈ vIn5 Hs T st (simAssemble st.params s ctr δ f), x ∈ Prover.gateInputsOff st.params T
      (pubOf Hs st s δ).iv (qcolsOf st (pubOf Hs st s δ) δ (ba f.1)) W128.zero := by
  have hacc := firstHit_accepts hf
  have hoc : openCount (ba δ) ≤ 105 := by
    unfold accepts at hacc; simp only [Bool.and_eq_true, decide_eq_true_eq] at hacc; exact hacc.2
  set pf : Proof := { params := st.params, bytes := simAssemble st.params s ctr δ f } with hpf
  have pfC : pf.corrections = ba f.1 :=
    (fields_assemble st.params _).1.trans (fit_of_size (size_ba _))
  have pfO : pf.opening = openingOf (ba δ) s.2.2.1 s.2.2.2 :=
    (fields_assemble st.params _).2.2.2.2.2.1.trans (fit_of_size (openingOf_size _ _ _ hoc))
  have pfD : pf.delta = ba δ := (fields_assemble st.params _).2.2.2.2.2.2.1.trans
    (fit_of_size (size_ba _))
  have pfI : pf.ivPre = ba s.1 := (fields_assemble st.params _).2.2.2.2.2.2.2.1.trans
    (fit_of_size (size_ba _))
  have hiv : ivOf Hs pf (st.mu1 Hs) = (pubOf Hs st s δ).iv := by rw [ivOf, pfI]; rfl
  intro x hx
  unfold vIn5 at hx
  simp only [← hpf, hiv, pfO, pfD] at hx
  split at hx
  · simp at hx
  · rename_i leaves hl
    have hP : (pubOf Hs st s δ).leaves = leaves := by
      show (BAVC.reconstruct (pubOf Hs st s δ).iv (openingOf (ba δ) s.2.2.1 s.2.2.2) (ba δ)).getD _ = _
      rw [hl]; rfl
    rw [gateInputs_eq_off] at hx
    have hco : pf.correctionOf = fun i =>
        (ba f.1).extract ((i - 1) * st.params.correctionBytes) (i * st.params.correctionBytes) := by
      funext i; rw [Proof.correctionOf, pfC]
    have hq : convertToVole pf (pubOf Hs st s δ).iv leaves =
        qcolsOf st (pubOf Hs st s δ) δ (ba f.1) := by
      rw [qcolsOf, hP, convertToVole, pfD, hco]
    rwa [hq] at hx

/-- **The verifier's `H₅` inputs on the ideal-tape prover's proof are its active gate inputs.** -/
theorem vIn5_proveIdeal (Hs' : Hashes) {cs : ByteArray → ByteArray → System GF128}
    (h : ZKHyp T st w cs) (s : Shared) (t : Pads st.params) {b : ByteArray}
    (hb : proveIdeal Hs' T st w (s, t) = .ok b) :
    ∀ x ∈ vIn5 Hs T st b, x ∈ actInputs Hs T st s t := by
  rw [proveIdeal_eq_outOf T st w cs Hs' h s t] at hb
  unfold outOf at hb
  rcases hf : firstHit s.2.1 with _ | ⟨ctr, δ⟩
  · rw [hf] at hb; cases hb
  · rw [hf] at hb
    simp only [Except.ok.injEq] at hb
    subst hb
    have hd : deltaOf s.2.1 = δ := by unfold deltaOf; rw [hf]; rfl
    intro x hx
    have := vIn5_simAssemble Hs T st s ctr δ _ hf x hx
    rw [actInputs, qcolsTape, hd, correctionsOf_eq]
    exact this

end Reads

/-! ## The hybrids, with the `H₂³` table visible -/

section Chain

variable (Hb : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)

/-- **The tables the distinguisher reads**: `H₃`, `H₂³` (on every grinding point) and `H₅`. -/
abbrev Vis2 (p : Params) := Tab3 × (Tab2G p × Tab5 p)

/-- The grinding prefix the simulator recomputes from an output (`vPre` with the `H₅` table; none
for an error). -/
noncomputable def outPre (G5 : Tab5 st.params) (o : Except String ByteArray) : ByteArray :=
  match o with
  | .ok b => vPre (rec5 Hb T st G5) T st b
  | .error _ => ByteArray.empty

/-- **The simulator's `H₂³` table**: `G2` programmed at the grinding points of the prefix
recomputed from the output (`outPre`), counter `c` answered by `g c`. -/
noncomputable def simTab (G5 : Tab5 st.params) (o : Except String ByteArray) (g : Grind)
    (G2 : Tab2G st.params) : Tab2G st.params :=
  programAt (key2 st.params (outPre Hb T st G5 o)) g G2

/-- The distinguisher, with the `H₂³` table programmed by `simTab` at the grinding answers `g`. -/
def Dp (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5 st.params → Prop)
    (o : Except String ByteArray) (g : Grind) (v : Vis2 st.params) : Prop :=
  D o v.1 (simTab Hb T st v.2.2 o g v.2.1) v.2.2

variable {Hb T st w}

lemma runE_agreeOff_h3' {Hs Hs' : Hashes} (h : Hs.AgreeOff .h3 Hs') :
    runE Hs T st w = runE Hs' T st w := runE_agreeOff_h3 h

variable (Hb T st w)

/-- **H1 with the tables** (`H₂³` visible): `rho` and the `H₃` table against a uniform seed and
`iv_pre`, for a distinguisher that reads the `H₃` table at `q₃` keys. -/
theorem joint2_h1 (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5 st.params → Prop)
    (Q3 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5 st.params → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G2 G5, (∀ k ∈ Q3 o G3 G2 G5, G3 k = G3' k) →
      (D o G3 G2 G5 ↔ D o G3' G2 G5))
    {q3 : ℕ} (hq3 : ∀ o G3 G2 G5, (Q3 o G3 G2 G5).card ≤ q3) :
    |pr ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5 st.params)) (fun c =>
        D (proveE (recH Hb T st w c.2.1 c.1.2 c.2.2) T st w aesTable (preR Hb T st w c.2.2) c.1.1)
          c.2.1 c.1.2 c.2.2) -
      pr (((Bytes 16 × Bytes 16) × Tab2G st.params) × (Tab3 × Tab5 st.params)) (fun c =>
        D (runE (recH Hb T st w c.2.1 c.1.2 c.2.2) T st w aesTable (preR Hb T st w c.2.2) c.1.1)
          c.2.1 c.1.2 c.2.2)| ≤ q3 / 2 ^ 128 := by
  let wP := w.extract 0 st.params.witnessBytes
  let E0 : (Tab2G st.params × Tab5 st.params) × (Bytes 16 × Tab3) ≃
      (Bytes 16 × Tab2G st.params) × (Tab3 × Tab5 st.params) :=
    { toFun := fun c => ((c.2.1, c.1.1), (c.2.2, c.1.2))
      invFun := fun c => ((c.1.2, c.2.2), (c.1.1, c.2.1))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let E1 : (Tab2G st.params × Tab5 st.params) × (Tab3 × (Bytes 16 × Bytes 16)) ≃
      ((Bytes 16 × Bytes 16) × Tab2G st.params) × (Tab3 × Tab5 st.params) :=
    { toFun := fun c => ((c.2.2, c.1.1), (c.2.1, c.1.2))
      invFun := fun c => ((c.1.2, c.2.2), (c.2.1, c.1.1))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv E0, ← pr_equiv E1]
  refine abs_pr_prod_sub_le _ _ fun a => ?_
  obtain ⟨G2, G5⟩ := a
  let R : Bytes 16 × Bytes 16 → Except String ByteArray :=
    runE (recH Hb T st w (fun _ => 0) G2 G5) T st w aesTable (preR Hb T st w G5)
  have hR : ∀ G3 : Tab3, runE (recH Hb T st w G3 G2 G5) T st w aesTable (preR Hb T st w G5) = R :=
    fun G3 => by rw [runE_agreeOff_h3' (recH_agreeOff_h3 _ (fun _ => 0) G2 G5)]
  let A : Bytes 16 × Bytes 16 → Tab3 → Prop := fun v G3 => D (R v) G3 G2 G5
  have h := h3_rom_query (st.mu1 Hb) wP Hb A (fun v G3 => Q3 (R v) G3 G2 G5)
    (fun v G3 G3' hk => hQ3 (R v) G3 G3' G2 G5 hk) (fun v G3 => hq3 _ G3 G2 G5)
  have e1 : pr (Bytes 16 × Tab3) (fun b => D (proveE (recH Hb T st w b.2 G2 G5) T st w aesTable
      (preR Hb T st w G5) b.1) b.2 G2 G5) = pr (Bytes 16 × (Bytes 16 → Bytes 32)) (fun p =>
        A (h3Seed (Hb.withTable .h3 (seedInput (st.mu1 Hb) wP) p.2) (st.mu1 Hb) wP (ba p.1)) p.2) := by
    refine pr_congr fun b => ?_
    simp only [A, proveE, recH_h3Seed, h3Seed_withTable, hR]
  have e2 : pr (Bytes 16 × ((Bytes 16 → Bytes 32) × Bytes 32)) (fun p => A (splitSeed p.2.2) p.2.1) =
      pr (Tab3 × (Bytes 16 × Bytes 16)) (fun b => D (runE (recH Hb T st w b.1 G2 G5) T st w
        aesTable (preR Hb T st w G5) b.2) b.1 G2 G5) := by
    rw [pr_prod_snd (α := Bytes 16) (fun q : (Bytes 16 → Bytes 32) × Bytes 32 => A (splitSeed q.2) q.1),
      ← pr_equiv (Equiv.prodCongr (Equiv.refl Tab3) splitEquiv)]
    refine pr_congr fun b => ?_
    simp only [A, hR]
    rfl
  have e1' : pr (Bytes 16 × Tab3) (fun b => D (proveE (recH Hb T st w b.2 G2 G5) T st w aesTable
      (preR Hb T st w G5) b.1) b.2 G2 G5) = pr (Bytes 16 × Tab3) (fun b =>
        D (proveE (recH Hb T st w (E0 ((G2, G5), b)).2.1 (E0 ((G2, G5), b)).1.2
          (E0 ((G2, G5), b)).2.2) T st w aesTable (preR Hb T st w (E0 ((G2, G5), b)).2.2)
          (E0 ((G2, G5), b)).1.1) (E0 ((G2, G5), b)).2.1 (E0 ((G2, G5), b)).1.2
          (E0 ((G2, G5), b)).2.2) := rfl
  have e2' : pr (Tab3 × (Bytes 16 × Bytes 16)) (fun b => D (runE (recH Hb T st w b.1 G2 G5) T st w
        aesTable (preR Hb T st w G5) b.2) b.1 G2 G5) = pr (Tab3 × (Bytes 16 × Bytes 16)) (fun b =>
        D (runE (recH Hb T st w (E1 ((G2, G5), b)).2.1 (E1 ((G2, G5), b)).1.2
          (E1 ((G2, G5), b)).2.2) T st w aesTable (preR Hb T st w (E1 ((G2, G5), b)).2.2)
          (E1 ((G2, G5), b)).1.1) (E1 ((G2, G5), b)).2.1 (E1 ((G2, G5), b)).1.2
          (E1 ((G2, G5), b)).2.2) := rfl
  rw [← e1', ← e2', e1, ← e2]
  exact h

/-- After grinding, with the grinding answers `G2`'s at the prover's prefix: the run of hybrid
H2's form. -/
lemma runE_recH (hHb : HashesWF Hb) {cs : ByteArray → ByteArray → System GF128}
    (h : ZKHypQ st w cs) (G3 : Tab3) (G2 : Tab2G st.params) (G5 : Tab5 st.params)
    (x : Bytes 16 × Bytes 16) :
    runE (recH Hb T st w G3 G2 G5) T st w aesTable (preR Hb T st w G5) x =
      hyb3 (recB Hb T st w G3 G5) T st w (x.2, G2 ∘ key2 st.params (preR Hb T st w G5 x))
        (hiddenOut st.params (ivOfPre Hb st x.2)
          (ba (deltaOf (G2 ∘ key2 st.params (preR Hb T st w G5 x)))) x.1) := by
  have hs : (preR Hb T st w G5 x).size = preLen st.params :=
    prePrefix_size _ T st w (hHb.withTable .h5 _ G5) h x
  unfold runE
  rw [recH_realGrind G3 G2 G5 hs, hyb3_agreeOff unread_h23 (recH_agreeOff_h23 G3 G2 (fun _ => 0) G5),
    recH_ivOfPre, ← hiddenOut_eq]
  rfl

/-- **Grinding with `H₂³` visible: programming is perfect** (exact). The grinding answers read off
the table at the prover's prefix, against independent uniform answers with the table programmed
with them there. -/
theorem joint2_prog (hHb : HashesWF Hb) {cs : ByteArray → ByteArray → System GF128}
    (h : ZKHypQ st w cs)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5 st.params → Prop) :
    |pr (((Bytes 16 × Bytes 16) × Tab2G st.params) × (Tab3 × Tab5 st.params)) (fun c =>
        D (runE (recH Hb T st w c.2.1 c.1.2 c.2.2) T st w aesTable (preR Hb T st w c.2.2) c.1.1)
          c.2.1 c.1.2 c.2.2) -
      pr (((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5 st.params)) (fun c =>
        D (hyb3 (recB Hb T st w c.2.1 c.2.2) T st w (c.1.1.2, c.1.2.2)
          (hiddenOut st.params (ivOfPre Hb st c.1.1.2) (ba (deltaOf c.1.2.2)) c.1.1.1))
          c.2.1 (programAt (key2 st.params (preR Hb T st w c.2.2 c.1.1)) c.1.2.2 c.1.2.1) c.2.2)| ≤
      0 := by
  refine abs_pr_prod_sub_le' _ _ fun v => ?_
  obtain ⟨G3, G5⟩ := v
  rw [abs_nonpos_iff, sub_eq_zero]
  have e := pr_program_eq (C := Bytes 16 × Bytes 16) (R := Bytes 16)
    (x := fun c => key2 st.params (preR Hb T st w G5 c)) (fun c => key2_injective _ _)
    (fun c (u : Grind) (G2 : Tab2G st.params) => D (hyb3 (recB Hb T st w G3 G5) T st w (c.2, u)
      (hiddenOut st.params (ivOfPre Hb st c.2) (ba (deltaOf u)) c.1)) G3 G2 G5)
  refine (pr_congr fun c => ?_).trans (e.trans (pr_congr fun c => Iff.rfl))
  simp only
  rw [runE_recH Hb T st w hHb h]

/-- **The programmed points, recomputed from the proof** (≤ `Pr[GrindBad]`): with the table
programmed at the grinding points of the prefix the verifier recomputes from the output
(`simTab`), instead of the prover's prefix. They agree unless the grinding outcome is bad
(`hyb3_vPre`, completeness of the recomputation). -/
theorem joint2_keys (hHb : HashesWF Hb) {cs : ByteArray → ByteArray → System GF128}
    (h : ZKHyp CrtGen.tables st w cs)
    (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5 st.params → Prop) :
    |pr (((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5 st.params)) (fun c =>
        D (hyb3 (recB Hb CrtGen.tables st w c.2.1 c.2.2) CrtGen.tables st w (c.1.1.2, c.1.2.2)
          (hiddenOut st.params (ivOfPre Hb st c.1.1.2) (ba (deltaOf c.1.2.2)) c.1.1.1))
          c.2.1 (programAt (key2 st.params (preR Hb CrtGen.tables st w c.2.2 c.1.1)) c.1.2.2 c.1.2.1)
          c.2.2) -
      pr (((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5 st.params)) (fun c =>
        Dp Hb CrtGen.tables st D (hyb3 (recB Hb CrtGen.tables st w c.2.1 c.2.2) CrtGen.tables st w
          (c.1.1.2, c.1.2.2)
          (hiddenOut st.params (ivOfPre Hb st c.1.1.2) (ba (deltaOf c.1.2.2)) c.1.1.1))
          c.1.2.2 (c.2.1, c.1.2.1, c.2.2))| ≤
      pr Grind (GrindBad CrtGen.tables) := by
  refine (abs_pr_sub_le_of_agree _ _ (fun c => GrindBad CrtGen.tables c.1.2.2) fun c hc => ?_).trans
    (le_of_eq ?_)
  · obtain ⟨⟨x, G2, g⟩, G3, G5⟩ := c
    have hwf : HashesWF (recB Hb CrtGen.tables st w G3 G5) := recH_wf hHb G3 _ G5
    dsimp only at hc ⊢
    obtain ⟨proof, hok, hv⟩ := hyb3_vPre hwf h hlab x g hc
    have hiv : ivOfPre (recB Hb CrtGen.tables st w G3 G5) st = ivOfPre Hb st :=
      recH_ivOfPre G3 (fun _ => 0) G5
    have hvp : vPre (recB Hb CrtGen.tables st w G3 G5) CrtGen.tables st =
        vPre (rec5 Hb CrtGen.tables st G5) CrtGen.tables st := vPre_recH G3 (fun _ => 0) G5
    have hpp : prePrefix (recB Hb CrtGen.tables st w G3 G5) CrtGen.tables st w =
        preR Hb CrtGen.tables st w G5 := prePrefix_recH G3 (fun _ => 0) G5
    rw [hiv] at hok
    rw [hvp, hpp] at hv
    simp only [Dp, simTab]
    rw [hok, outPre, hv]
  · rw [pr_prod_fst (β := Tab3 × Tab5 st.params)
      (fun a : (Bytes 16 × Bytes 16) × (Tab2G st.params × Grind) => GrindBad CrtGen.tables a.2.2),
      pr_prod_snd (α := Bytes 16 × Bytes 16)
        (fun a : Tab2G st.params × Grind => GrindBad CrtGen.tables a.2),
      pr_prod_snd (α := Tab2G st.params) (GrindBad CrtGen.tables)]

/-- **H4 with the tables** (BAVC hiding for AES assumed, `HideHyp`): the hidden part of the
commitment from a uniform root seed against the ideal hidden part, for a distinguisher that also
sees the grinding answers (through the programmed `H₂³` table) and all the tables. -/
theorem joint2_h4 (hHb : HashesWF Hb) {εb : ℝ} (hH : HideHyp st.params εb)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5 st.params → Prop) :
    |pr (((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5 st.params)) (fun c =>
        Dp Hb T st D (hyb3 (recB Hb T st w c.2.1 c.2.2) T st w (c.1.1.2, c.1.2.2)
          (hiddenOut st.params (ivOfPre Hb st c.1.1.2) (ba (deltaOf c.1.2.2)) c.1.1.1))
          c.1.2.2 (c.2.1, c.1.2.1, c.2.2)) -
      pr ((Hidden st.params × (Bytes 16 × Grind)) × Vis2 st.params) (fun c =>
        Dp Hb T st D (hyb3 (recB Hb T st w c.2.1 c.2.2.2) T st w c.1.2
          (hiddenIdeal (ba (deltaOf c.1.2.2)) c.1.1)) c.1.2.2 c.2)| ≤ εb := by
  let E2 : ((Bytes 16 × Grind) × Vis2 st.params) × Bytes 16 ≃
      ((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5 st.params) :=
    { toFun := fun c => (((c.2, c.1.1.1), (c.1.2.2.1, c.1.1.2)), (c.1.2.1, c.1.2.2.2))
      invFun := fun c => (((c.1.1.2, c.1.2.2), (c.2.1, c.1.2.1, c.2.2)), c.1.1.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let E3 : ((Bytes 16 × Grind) × Vis2 st.params) × Hidden st.params ≃
      (Hidden st.params × (Bytes 16 × Grind)) × Vis2 st.params :=
    { toFun := fun c => ((c.2, c.1.1), c.1.2)
      invFun := fun c => ((c.1.2, c.2), c.1.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv E2, ← pr_equiv E3]
  refine abs_pr_prod_sub_le _ _ fun a => ?_
  obtain ⟨b, v⟩ := a
  exact hH (ivOfPre Hb st b.1) (deltaOf b.2) (hHb .h4 _)
    (fun hid => Dp Hb T st D (hyb3 (recB Hb T st w v.1 v.2.2) T st w b hid) b.2 v)

/-- **The deterministic steps with the tables** (exact): the unused seed slots, then the tape. -/
theorem joint2_tape (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5 st.params → Prop) :
    |pr ((Hidden st.params × (Bytes 16 × Grind)) × Vis2 st.params) (fun c =>
        Dp Hb T st D (hyb3 (recB Hb T st w c.2.1 c.2.2.2) T st w c.1.2
          (hiddenIdeal (ba (deltaOf c.1.2.2)) c.1.1)) c.1.2.2 c.2) -
      pr (IdealTape st.params × Vis2 st.params) (fun c =>
        Dp Hb T st D (proveIdeal (recB Hb T st w c.2.1 c.2.2.2) T st w
          (fillSib (recB Hb T st w c.2.1 c.2.2.2) T st c.1)) c.1.1.2.1 c.2)| ≤ 0 := by
  refine abs_pr_prod_sub_le' _ _ fun v => ?_
  rw [abs_nonpos_iff, sub_eq_zero]
  set R := recB Hb T st w v.1 v.2.2
  let F : Except String ByteArray → Grind → Prop := fun o g => Dp Hb T st D o g v
  have e1 : pr (Hidden st.params × (Bytes 16 × Grind)) (fun y =>
      F (hyb3 R T st w y.2 (hiddenIdeal (ba (deltaOf y.2.2)) y.1)) y.2.2) =
      pr (Hidden st.params × (Bytes 16 × Grind)) (fun y => F (hyb3 R T st w y.2 y.1) y.2.2) :=
    pr_congr fun y => by rw [hyb3_zeroTail]
  have e2 : pr (IdealTape st.params) (fun t => F (proveIdeal R T st w (fillSib R T st t)) t.1.2.1) =
      pr (Hidden st.params × (Bytes 16 × Grind)) (fun y => F (hyb3 R T st w y.2 y.1) y.2.2) := by
    rw [← pr_equiv (tapeEquiv st.params), ← pr_prod_fst (β := Sib)
      (fun y : Hidden st.params × (Bytes 16 × Grind) => F (hyb3 R T st w y.2 y.1) y.2.2)]
    refine pr_congr fun x => ?_
    rw [show tapeEquiv st.params x = tapeOfHidden x.1.2.1 x.1.2.2 x.1.1 x.2 from rfl, hyb3,
      fillSib_tapeOfHidden R T st _ _ _ x.2 fun _ => fun _ => 0]
    rfl
  exact e1.trans e2.symm

lemma vIn5_congr {Hs Hs' : Hashes} (hmu : st.mu1 Hs = st.mu1 Hs') (h4 : Hs.hash .h4 = Hs'.hash .h4) :
    vIn5 Hs T st = vIn5 Hs' T st := by
  funext b
  simp only [vIn5, ivOf, hmu, h4]

/-- **H6 with the tables**: the sibling answers recomputed from the `H₅` table against uniform
ones, for a distinguisher that reads the `H₅` table at `q₅` keys (and sees the other tables and,
through the programmed `H₂³` table, the grinding answers). The simulator's recomputation of the
grinding prefix reads `H₅` only at the prover's own active inputs (`vIn5_proveIdeal`), so it adds
no reads. -/
theorem joint2_h6 {cs : ByteArray → ByteArray → System GF128} (hlr : st.params.labelRows = true)
    (hzk : ZKHyp T st w cs)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5 st.params → Prop)
    (Q5 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5 st.params →
      Finset (SKey st.params))
    (hQ5 : ∀ o G3 G2 G5 G5', (∀ k ∈ Q5 o G3 G2 G5, G5 k = G5' k) →
      (D o G3 G2 G5 ↔ D o G3 G2 G5'))
    {q5 : ℕ} (hq5 : ∀ o G3 G2 G5, (Q5 o G3 G2 G5).card ≤ q5) :
    |pr (IdealTape st.params × Vis2 st.params) (fun c =>
        Dp Hb T st D (proveIdeal (recB Hb T st w c.2.1 c.2.2.2) T st w
          (fillSib (recB Hb T st w c.2.1 c.2.2.2) T st c.1)) c.1.1.2.1 c.2) -
      pr (IdealTape st.params × Vis2 st.params) (fun c =>
        Dp Hb T st D (proveIdeal (recB Hb T st w c.2.1 c.2.2.2) T st w c.1) c.1.1.2.1 c.2)| ≤
      (q5 + 1) / 2 ^ 128 := by
  obtain ⟨h1, -, -, h2⟩ := labelRows_sizes hlr
  have hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows := by omega
  let E6 : (Tab3 × Tab2G st.params) × (IdealTape st.params × Tab5 st.params) ≃
      IdealTape st.params × Vis2 st.params :=
    { toFun := fun c => (c.2.1, (c.1.1, (c.1.2, c.2.2)))
      invFun := fun c => ((c.2.1, c.2.2.1), (c.1, c.2.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv E6, ← pr_equiv E6]
  refine abs_pr_prod_sub_le _ _ fun a => ?_
  obtain ⟨G3, G2⟩ := a
  set base := (Hb.withTable .h3 (seedInput (st.mu1 Hb) (w.extract 0 st.params.witnessBytes)) G3
    ).withTable .h23 (enc2 st.params) (fun _ => 0) with hbase
  have a1 := Hb.agreeOff_withTable .h3 (seedInput (st.mu1 Hb) (w.extract 0 st.params.witnessBytes)) G3
  have a2 := (Hb.withTable .h3 (seedInput (st.mu1 Hb) (w.extract 0 st.params.witnessBytes)) G3
    ).agreeOff_withTable .h23 (enc2 st.params) (fun _ => 0)
  have hsE : sEnc base T st = sEnc Hb T st :=
    ((sEnc_agreeOff unread_h3 a1 T st).trans (sEnc_agreeOff unread_h23 a2 T st)).symm
  have hv5 : ∀ G : Tab5 st.params, vIn5 (rec5 Hb T st G) T st = vIn5 base T st := by
    intro G
    have a0 := Hb.agreeOff_withTable .h5 (sEnc Hb T st) G
    refine vIn5_congr T st ?_ ?_
    · exact (a0.mu1 (by decide) (by decide) st).symm.trans
        ((a1.mu1 (by decide) (by decide) st).trans (a2.mu1 (by decide) (by decide) st))
    · exact (a0 .h4 (by decide)).symm.trans ((a1 .h4 (by decide)).trans (a2 .h4 (by decide)))
  have hA : ∀ (t : IdealTape st.params) (G G' : Tab5 st.params), (∀ k ∈ proverKeys base T st t ∪
      (fun o (s : Shared) G5 => Q5 o G3 (simTab Hb T st G5 o s.2.1 G2) G5)
        (proveIdeal (H5 base T st G) T st w t) t.1 G, G k = G' k) →
      ((fun o (s : Shared) G5 => Dp Hb T st D o s.2.1 (G3, G2, G5))
          (proveIdeal (H5 base T st G) T st w t) t.1 G ↔
        (fun o (s : Shared) G5 => Dp Hb T st D o s.2.1 (G3, G2, G5))
          (proveIdeal (H5 base T st G') T st w t) t.1 G') := by
    intro t G G' hG
    have hp := proveIdeal_table_congr base T st w hlab t G G'
      fun k hk => hG k (Finset.mem_union_left _ hk)
    have hpre : outPre Hb T st G (proveIdeal (H5 base T st G) T st w t) =
        outPre Hb T st G' (proveIdeal (H5 base T st G) T st w t) := by
      rcases ho : proveIdeal (H5 base T st G) T st w t with e | b
      · rfl
      · simp only [outPre]
        have hag : (rec5 Hb T st G).AgreeOff .h5 (rec5 Hb T st G') :=
          Hashes.AgreeOff.withTable_same (k := .h5) (Hs := Hb) (Hs' := Hb) (fun _ _ => rfl) (sEnc Hb T st)
            (sEnc Hb T st) G G'
        refine vPre_h5_congr hag T st b fun x hx => ?_
        rw [hv5] at hx
        have hx' : x ∈ actInputs base T st t.1 t.2 :=
          vIn5_proveIdeal base T st w (H5 base T st G) hzk t.1 t.2 ho x hx
        simp only [rec5, Hashes.withTable, ↓reduceIte]
        split
        · rename_i hy
          have hk : hy.choose ∈ proverKeys base T st t := by
            rw [mem_proverKeys, hsE, hy.choose_spec]; exact hx'
          exact congrArg ba (hG _ (Finset.mem_union_left _ hk))
        · rfl
    have hX : simTab Hb T st G' (proveIdeal (H5 base T st G') T st w t) t.1.2.1 G2 =
        simTab Hb T st G (proveIdeal (H5 base T st G) T st w t) t.1.2.1 G2 := by
      unfold simTab
      rw [← hp, ← hpre]
    show D (proveIdeal (H5 base T st G) T st w t) G3
        (simTab Hb T st G (proveIdeal (H5 base T st G) T st w t) t.1.2.1 G2) G ↔
      D (proveIdeal (H5 base T st G') T st w t) G3
        (simTab Hb T st G' (proveIdeal (H5 base T st G') T st w t) t.1.2.1 G2) G'
    rw [hX, ← hp]
    exact hQ5 _ G3 _ G G' fun k hk => hG k (Finset.mem_union_right _ hk)
  have h := lab_rom_hyp_s base T st w cs hlr hzk
    (fun o (s : Shared) G5 => Dp Hb T st D o s.2.1 (G3, G2, G5))
    (fun o (s : Shared) G5 => Q5 o G3 (simTab Hb T st G5 o s.2.1 G2) G5) hA
    (fun o s G => hq5 _ _ _ _)
  have hR : ∀ G5, H5 base T st G5 = recB Hb T st w G3 G5 := fun G5 => (recB_eq_H5 G3 G5).symm
  simp only [hR] at h
  exact h

/-- **The ideal-tape prover on a uniform tape is the simulator**, with the tables and the
grinding answers (exact). -/
theorem joint2_sim {cs : ByteArray → ByteArray → System GF128} (hzk : ZKHyp T st w cs)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5 st.params → Prop) :
    |pr (IdealTape st.params × Vis2 st.params) (fun c =>
        Dp Hb T st D (proveIdeal (recB Hb T st w c.2.1 c.2.2.2) T st w c.1) c.1.1.2.1 c.2) -
      pr (SimCoins st.params × Vis2 st.params) (fun c =>
        Dp Hb T st D (simulate st.params c.1) c.1.1.2.1 c.2)| ≤ 0 :=
  abs_pr_prod_sub_le' _ _ fun v => by
    have := proveIdeal_close_shared (recB Hb T st w v.1 v.2.2) T st w cs hzk
      (fun os => Dp Hb T st D os.1 os.2.2.1 v)
    dsimp only at this ⊢
    exact this

/-! ## The end-to-end statement -/

lemma abs_chain7 {a0 a1 a2 a3 a4 a5 a6 a7 e1 e2 e3 e4 e5 e6 e7 : ℝ} (h1 : |a0 - a1| ≤ e1)
    (h2 : |a1 - a2| ≤ e2) (h3 : |a2 - a3| ≤ e3) (h4 : |a3 - a4| ≤ e4) (h5 : |a4 - a5| ≤ e5)
    (h6 : |a5 - a6| ≤ e6) (h7 : |a6 - a7| ≤ e7) :
    |a0 - a7| ≤ e1 + e2 + e3 + e4 + e5 + e6 + e7 := by
  have := abs_sub_le a0 a1 a7
  have := abs_sub_le a1 a2 a7
  have := abs_sub_le a2 a3 a7
  have := abs_sub_le a3 a4 a7
  have := abs_sub_le a4 a5 a7
  have := abs_sub_le a5 a6 a7
  linarith

/-- **Zero knowledge in the random-oracle model with the `H₂³` table visible** (label-row layout,
faest-arch-opt's tables, one statement and witness).

The hash record is `recH Hb … G3 G2 G5`: the base record `Hb` with `H₃` a uniform table `G3` on
the seed inputs, `H₂³` a uniform table `G2` on **every** grinding point `pre ‖ ctr ‖ 11` with a
`preLen`-byte prefix, and `H₅` a uniform table `G5` on the sibling inputs (every other domain, and
these domains elsewhere, are `Hb`'s). The real world is the **executable prover** `Prover.prove`
with this record and a uniform `rho`.

The simulator outputs `simulate` (from its coins only) and the `H₂³` table `simTab`: `G2`
programmed at the grinding points of the prefix `chal2 ‖ qs_check ‖ ã` it recomputes from its own
proof as the verifier does (`vPre`, with the `H₅` table; `vPre_eq_verify`: the points of
`simulateRO`), counter `c` answered by its grinding tape at `c` (so `Δ` at its counter).

A distinguisher `D` sees the output and all three tables, reads `H₃` and `H₅` adaptively at `q₃`
and `q₅` keys (`Q3`, `Q5`: each condition says that `D` does not depend on the table outside
them, with the others fixed), and **reads the `H₂³` table freely** (no bound). Assumed: BAVC hiding
for AES (`HideHyp`, `ε_bavc`). Its advantage is at most

    q₃·2⁻¹²⁸ + Pr[GrindBad] + ε_bavc + (q₅ + 1)·2⁻¹²⁸

(H1; grinding and programming, exact; recomputing the programmed points from the proof, which
agrees with the prover's points unless no grinding answer is accepted or the lifted `Δ'` is zero;
H4; H6). There is no `q₂` term: programming the table is perfect (`pr_program_eq`), and the
recomputed points are the prover's (`hyb3_vPre`). -/
theorem zk_rom_h23 {cs : ByteArray → ByteArray → System GF128} (hlr : st.params.labelRows = true)
    (hzk : ZKHyp CrtGen.tables st w cs) (hHb : HashesWF Hb) {εb : ℝ} (hH : HideHyp st.params εb)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5 st.params → Prop)
    (Q3 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5 st.params → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G2 G5, (∀ k ∈ Q3 o G3 G2 G5, G3 k = G3' k) →
      (D o G3 G2 G5 ↔ D o G3' G2 G5))
    {q3 : ℕ} (hq3 : ∀ o G3 G2 G5, (Q3 o G3 G2 G5).card ≤ q3)
    (Q5 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5 st.params →
      Finset (SKey st.params))
    (hQ5 : ∀ o G3 G2 G5 G5', (∀ k ∈ Q5 o G3 G2 G5, G5 k = G5' k) →
      (D o G3 G2 G5 ↔ D o G3 G2 G5'))
    {q5 : ℕ} (hq5 : ∀ o G3 G2 G5, (Q5 o G3 G2 G5).card ≤ q5) :
    |pr ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5 st.params)) (fun c =>
        D (Prover.prove (recH Hb CrtGen.tables st w c.2.1 c.1.2 c.2.2) CrtGen.tables st w (ba c.1.1))
          c.2.1 c.1.2 c.2.2) -
      pr (SimCoins st.params × Vis2 st.params) (fun c =>
        D (simulate st.params c.1) c.2.1
          (simTab Hb CrtGen.tables st c.2.2.2 (simulate st.params c.1) c.1.1.2.1 c.2.2.1) c.2.2.2)| ≤
      q3 / 2 ^ 128 + pr Grind (GrindBad CrtGen.tables) + εb + (q5 + 1) / 2 ^ 128 := by
  obtain ⟨hl1, -, -, hl2⟩ := labelRows_sizes hlr
  have hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows := by omega
  have e0 : pr ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5 st.params)) (fun c =>
      D (Prover.prove (recH Hb CrtGen.tables st w c.2.1 c.1.2 c.2.2) CrtGen.tables st w (ba c.1.1))
        c.2.1 c.1.2 c.2.2) =
      pr ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5 st.params)) (fun c =>
        D (proveE (recH Hb CrtGen.tables st w c.2.1 c.1.2 c.2.2) CrtGen.tables st w aesTable
          (preR Hb CrtGen.tables st w c.2.2) c.1.1) c.2.1 c.1.2 c.2.2) := by
    refine pr_congr fun c => ?_
    have hR : RunHyp (recH Hb CrtGen.tables st w c.2.1 c.1.2 c.2.2) CrtGen.tables st w cs :=
      ⟨hzk, recH_wf hHb _ _ _, bavcComplete, fun rho => crtComplete _ _ _ _ rho _ hlab, hlab⟩
    rw [← proveE_aes _ CrtGen.tables st w hR c.1.1, prePrefix_recH]
  rw [e0]
  have h1 := joint2_h1 Hb CrtGen.tables st w D Q3 hQ3 hq3
  have h2 := joint2_prog Hb CrtGen.tables st w hHb hzk.q D
  have h3 := joint2_keys Hb st w hHb hzk hlab D
  have h4 := joint2_h4 Hb CrtGen.tables st w hHb hH D
  have h5 := joint2_tape Hb CrtGen.tables st w D
  have h6 := joint2_h6 Hb CrtGen.tables st w hlr hzk D Q5 hQ5 hq5
  have h7 := joint2_sim Hb CrtGen.tables st w hzk D
  exact (abs_chain7 h1 h2 h3 h4 h5 h6 h7).trans (le_of_eq (by ring))

end Chain

/-! ## Programming only the counters up to the simulator's own (as `simulateRO`) -/

section RO

lemma findFirst_ge {α : Type} (f : ℕ → Option α) (idx : α → ℕ)
    (hidx : ∀ k a, f k = some a → idx a = k) :
    ∀ (n c : ℕ) {a : α}, Prover.findFirst f n c = some a → c ≤ idx a
  | 0, _, _, h => by simp [Prover.findFirst] at h
  | n + 1, c, a, h => by
    simp only [Prover.findFirst] at h
    cases hfc : f c with
    | some b => rw [hfc] at h; cases h; exact (hidx c _ hfc).ge
    | none => rw [hfc] at h; exact (findFirst_ge f idx hidx n (c + 1) h).trans' (Nat.le_succ c)

lemma findFirst_congr_le {α : Type} {f g : ℕ → Option α} (idx : α → ℕ)
    (hidx : ∀ k a, f k = some a → idx a = k) :
    ∀ (n c : ℕ) {a : α}, Prover.findFirst f n c = some a →
      (∀ k, c ≤ k → k ≤ idx a → f k = g k) → Prover.findFirst g n c = some a
  | 0, _, _, h, _ => by simp [Prover.findFirst] at h
  | n + 1, c, a, h, hfg => by
    have hge := findFirst_ge f idx hidx (n + 1) c h
    have hc := hfg c le_rfl hge
    simp only [Prover.findFirst] at h ⊢
    rw [← hc]
    cases hfc : f c with
    | some b => rw [hfc] at h; exact h
    | none =>
      rw [hfc] at h
      exact findFirst_congr_le idx hidx n (c + 1) h fun k h1 h2 => hfg k (by omega) h2

/-- **The grinding outcome depends on the answers up to the accepted counter only.** -/
lemma firstHit_congr_le {g g' : Grind} {ctr : ℕ} {d : Bytes 16} (h : firstHit g = some (ctr, d))
    (hg : ∀ c : Fin nGrind, c.val ≤ ctr → g' c = g c) : firstHit g' = some (ctr, d) := by
  unfold firstHit at h ⊢
  refine findFirst_congr_le (fun x : ℕ × Bytes 16 => x.1) (fun k a hk => ?_) nGrind 0 h
    fun k _ hk => ?_
  · split at hk
    · split at hk
      · cases hk; rfl
      · cases hk
    · cases hk
  · dsimp only at hk
    split
    · rename_i hk'
      rw [hg ⟨k, hk'⟩ hk]
    · rfl

/-- The simulator's counter (`nGrind`, i.e. every counter, if no answer is accepted). -/
def hitCtr (g : Grind) : ℕ :=
  match firstHit g with
  | some (c, _) => c
  | none => nGrind

lemma firstHit_congr_hitCtr {g g' : Grind} (hg : ∀ c : Fin nGrind, c.val ≤ hitCtr g → g' c = g c) :
    firstHit g' = firstHit g := by
  rcases h : firstHit g with _ | ⟨ctr, d⟩
  · have : g' = g := funext fun c => hg c (by simp only [hitCtr, h]; exact c.isLt.le)
    rw [this, h]
  · exact firstHit_congr_le h fun c hc => hg c (by simp only [hitCtr, h]; exact hc)

variable (Hb : Hashes) (T : CrtTables) (st : Statement)

/-- **The simulator's `H₂³` table, as `simulateRO` programs it**: `G2` programmed at the grinding
points of the recomputed prefix for the counters `c ≤ ctr` only (`Δ` at `ctr`, the rejected
answers below; every counter if grinding failed). -/
noncomputable def simTabRO (G5 : Tab5 st.params) (o : Except String ByteArray) (g : Grind)
    (G2 : Tab2G st.params) : Tab2G st.params :=
  programAt (key2 st.params (outPre Hb T st G5 o))
    (fun c => if c.val ≤ hitCtr g then g c else G2 (key2 st.params (outPre Hb T st G5 o) c)) G2

lemma simulate_congr {s s' : Shared} (f : SimFields st.params) (h1 : s'.1 = s.1)
    (h2 : firstHit s'.2.1 = firstHit s.2.1) (h3 : s'.2.2 = s.2.2) :
    simulate st.params (s', f) = simulate st.params (s, f) := by
  obtain ⟨a, g, r⟩ := s
  obtain ⟨a', g', r'⟩ := s'
  dsimp only at h1 h2 h3
  subst h1 h3
  simp only [simulate, h2, publicFields]

/-- The swap of the grinding answers past the counter `n` with the table's answers at the
prefix block `P` there. -/
def swapG (n : ℕ) (P : Bytes (preLen st.params)) (g : Grind) (G2 : Tab2G st.params) :
    Grind × Tab2G st.params :=
  (fun k => if k.val ≤ n then g k else G2 (P, k),
    fun key => if key.1 = P ∧ n < key.2.val then g key.2 else G2 key)

lemma swapG_swapG (n : ℕ) (P : Bytes (preLen st.params)) (g : Grind) (G2 : Tab2G st.params) :
    swapG st n P (swapG st n P g G2).1 (swapG st n P g G2).2 = (g, G2) := by
  refine Prod.ext ?_ ?_
  · funext k
    by_cases h1 : k.val ≤ n
    · simp only [swapG, h1, ↓reduceIte]
    · have h2 : n < k.val := by omega
      simp only [swapG, h1, h2, and_self, ↓reduceIte]
  · funext key
    by_cases h1 : key.1 = P ∧ n < key.2.val
    · have h2 : ¬ key.2.val ≤ n := by omega
      simp only [swapG, h1, h2, and_self, ↓reduceIte]
      rw [← h1.1]
    · simp only [swapG, h1, ↓reduceIte]

/-- The coins with the grinding answers and the `H₂³` table replaced. -/
def withGG (c : SimCoins st.params × Vis2 st.params) (x : Grind × Tab2G st.params) :
    SimCoins st.params × Vis2 st.params :=
  (((c.1.1.1, x.1, c.1.1.2.2), c.1.2), (c.2.1, x.2, c.2.2.2))

/-- The simulator's recomputed prefix block. -/
noncomputable def pOf (c : SimCoins st.params × Vis2 st.params) : Bytes (preLen st.params) :=
  blk (preLen st.params) (outPre Hb T st c.2.2.2 (simulate st.params c.1))

/-- The swap of the coins. -/
noncomputable def roSwap (c : SimCoins st.params × Vis2 st.params) : SimCoins st.params × Vis2 st.params :=
  withGG st c (swapG st (hitCtr c.1.1.2.1) (pOf Hb T st c) c.1.1.2.1 c.2.2.1)

lemma roSwap_fixed (c : SimCoins st.params × Vis2 st.params) :
    hitCtr (roSwap Hb T st c).1.1.2.1 = hitCtr c.1.1.2.1 ∧
      simulate st.params (roSwap Hb T st c).1 = simulate st.params c.1 ∧
      pOf Hb T st (roSwap Hb T st c) = pOf Hb T st c := by
  have hf : firstHit (roSwap Hb T st c).1.1.2.1 = firstHit c.1.1.2.1 :=
    firstHit_congr_hitCtr fun k hk => by
      show (if k.val ≤ hitCtr c.1.1.2.1 then _ else _) = _
      simp only [hk, ↓reduceIte]
  have hs : simulate st.params (roSwap Hb T st c).1 = simulate st.params c.1 :=
    simulate_congr st c.1.2 rfl hf rfl
  refine ⟨by simp only [hitCtr, hf], hs, ?_⟩
  unfold pOf
  rw [hs]
  rfl

lemma roSwap_involutive : Function.Involutive (roSwap Hb T st) := by
  intro c
  obtain ⟨hn, -, hp⟩ := roSwap_fixed Hb T st c
  have e : roSwap Hb T st (roSwap Hb T st c) = withGG st (roSwap Hb T st c)
      (swapG st (hitCtr (roSwap Hb T st c).1.1.2.1) (pOf Hb T st (roSwap Hb T st c))
        (roSwap Hb T st c).1.1.2.1 (roSwap Hb T st c).2.2.1) := rfl
  rw [e, hn, hp]
  show withGG st (withGG st c (swapG st (hitCtr c.1.1.2.1) (pOf Hb T st c) c.1.1.2.1 c.2.2.1))
    (swapG st (hitCtr c.1.1.2.1) (pOf Hb T st c)
      (swapG st (hitCtr c.1.1.2.1) (pOf Hb T st c) c.1.1.2.1 c.2.2.1).1
      (swapG st (hitCtr c.1.1.2.1) (pOf Hb T st c) c.1.1.2.1 c.2.2.1).2) = c
  rw [swapG_swapG]
  rfl

lemma simTabRO_roSwap (c : SimCoins st.params × Vis2 st.params) :
    simTabRO Hb T st (roSwap Hb T st c).2.2.2 (simulate st.params c.1)
      (roSwap Hb T st c).1.1.2.1 (roSwap Hb T st c).2.2.1 =
      simTab Hb T st c.2.2.2 (simulate st.params c.1) c.1.1.2.1 c.2.2.1 := by
  obtain ⟨hn, -, -⟩ := roSwap_fixed Hb T st c
  have e1 : (roSwap Hb T st c).2.2.2 = c.2.2.2 := rfl
  have e2 : (roSwap Hb T st c).1.1.2.1 = (swapG st (hitCtr c.1.1.2.1) (pOf Hb T st c) c.1.1.2.1
      c.2.2.1).1 := rfl
  have e3 : (roSwap Hb T st c).2.2.1 = (swapG st (hitCtr c.1.1.2.1) (pOf Hb T st c) c.1.1.2.1
      c.2.2.1).2 := rfl
  have hP : pOf Hb T st c = (key2 st.params (outPre Hb T st c.2.2.2 (simulate st.params c.1)) 0).1 :=
    rfl
  unfold simTabRO
  rw [e1, hn, e2, e3]
  unfold simTab
  set P := outPre Hb T st c.2.2.2 (simulate st.params c.1)
  funext key
  by_cases hk : ∃ k, key2 st.params P k = key
  · obtain ⟨k, rfl⟩ := hk
    rw [programAt_apply_pt (key2_injective _ _), programAt_apply_pt (key2_injective _ _)]
    by_cases h1 : k.val ≤ hitCtr c.1.1.2.1
    · simp only [swapG, h1, ↓reduceIte]
    · have h2 : hitCtr c.1.1.2.1 < k.val := by omega
      simp only [swapG, hP, key2, h1, h2, and_self, ↓reduceIte]
  · push Not at hk
    rw [programAt_apply_of_ne _ _ hk, programAt_apply_of_ne _ _ hk]
    have hne : ¬ (key.1 = pOf Hb T st c ∧ hitCtr c.1.1.2.1 < key.2.val) := by
      rintro ⟨h1, -⟩
      refine hk key.2 ?_
      obtain ⟨k1, k2⟩ := key
      dsimp only at h1 ⊢
      rw [h1, hP]
      rfl
    simp only [swapG, hne, ↓reduceIte]

/-- **Programming the counters past the simulator's own is not needed** (exact): the simulator
that programs `H₂³` at every counter of its recomputed prefix (`simTab`) and the one that programs
only `c ≤ ctr` (`simTabRO`, the points of `simulateRO`) have the same law against every
distinguisher. -/
theorem sim_ro_eq (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5 st.params → Prop) :
    pr (SimCoins st.params × Vis2 st.params) (fun c =>
        D (simulate st.params c.1) c.2.1
          (simTab Hb T st c.2.2.2 (simulate st.params c.1) c.1.1.2.1 c.2.2.1) c.2.2.2) =
      pr (SimCoins st.params × Vis2 st.params) (fun c =>
        D (simulate st.params c.1) c.2.1
          (simTabRO Hb T st c.2.2.2 (simulate st.params c.1) c.1.1.2.1 c.2.2.1) c.2.2.2) := by
  rw [← pr_equiv (roSwap_involutive Hb T st).toPerm]
  refine pr_congr fun c => ?_
  simp only [Function.Involutive.coe_toPerm]
  obtain ⟨-, hs, -⟩ := roSwap_fixed Hb T st c
  have L := simTabRO_roSwap Hb T st (roSwap Hb T st c)
  rw [roSwap_involutive Hb T st c, hs] at L
  rw [hs, ← L]
  rfl

variable (w : ByteArray)

/-- The bad grinding outcomes: no accepted answer (`noHitProb`, the abort term of the two-phase
prover) or a zero lifted `Δ'`. -/
lemma grindBad_le : pr Grind (GrindBad T) ≤
    pr Grind (fun g => firstHit g = none) + pr Grind (fun g => tDL T (deltaOf g) = 0) :=
  pr_or_le _ _

/-- **`zk_rom_h23` for the simulator of `simulateRO`**: the same bound with the simulator
programming `H₂³` only at its counters `c ≤ ctr` (`Δ` at `ctr`, its rejected answers below) of
the prefix it recomputes from its proof. -/
theorem zk_rom_h23_ro {cs : ByteArray → ByteArray → System GF128} (hlr : st.params.labelRows = true)
    (hzk : ZKHyp CrtGen.tables st w cs) (hHb : HashesWF Hb) {εb : ℝ} (hH : HideHyp st.params εb)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5 st.params → Prop)
    (Q3 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5 st.params → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G2 G5, (∀ k ∈ Q3 o G3 G2 G5, G3 k = G3' k) →
      (D o G3 G2 G5 ↔ D o G3' G2 G5))
    {q3 : ℕ} (hq3 : ∀ o G3 G2 G5, (Q3 o G3 G2 G5).card ≤ q3)
    (Q5 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5 st.params →
      Finset (SKey st.params))
    (hQ5 : ∀ o G3 G2 G5 G5', (∀ k ∈ Q5 o G3 G2 G5, G5 k = G5' k) →
      (D o G3 G2 G5 ↔ D o G3 G2 G5'))
    {q5 : ℕ} (hq5 : ∀ o G3 G2 G5, (Q5 o G3 G2 G5).card ≤ q5) :
    |pr ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5 st.params)) (fun c =>
        D (Prover.prove (recH Hb CrtGen.tables st w c.2.1 c.1.2 c.2.2) CrtGen.tables st w (ba c.1.1))
          c.2.1 c.1.2 c.2.2) -
      pr (SimCoins st.params × Vis2 st.params) (fun c =>
        D (simulate st.params c.1) c.2.1
          (simTabRO Hb CrtGen.tables st c.2.2.2 (simulate st.params c.1) c.1.1.2.1 c.2.2.1)
          c.2.2.2)| ≤
      q3 / 2 ^ 128 + pr Grind (GrindBad CrtGen.tables) + εb + (q5 + 1) / 2 ^ 128 := by
  rw [← sim_ro_eq]
  exact zk_rom_h23 Hb st w hlr hzk hHb hH D Q3 hQ3 hq3 Q5 hQ5 hq5

end RO

end VoleMole.ZK.Sim
