import VoleMole.ZK.CollideRO
import VoleMole.ZK.HopsPatch
import VoleMole.Privacy.Resample
import VoleMole.Privacy.AdaptiveRO

/-!
# Zero knowledge for a statement chosen by an adversary that reads the tables

`zk_ro` (`ZK/ReadsRO.lean`) is for a statement and witness fixed before the random tables are
drawn. Here they are chosen by an adversary `S` that reads the tables first (`H₃` slice, `H₂³`,
`H₅`, the cipher, at `s₃`, `s₂`, `s₅`, `s_E` keys, adaptively), then the proof is produced, and a
distinguisher sees `S`'s output, the proof and the tables.

**The reduction** (`Privacy.pr_resample`). `S`'s output is a function of the tables on its query
sets, so given its view the tables are uniform off those sets: both experiments are averages, over
the outer tables `a` (fixing the statement `S a` and the query sets `Q a`), of the experiments on a
fresh uniform table **patched** with `a` on `Q a` (`mixT`). For a fixed statement and fixed patches
(`zk_patched`):

* the `H₅` and cipher patches go through the chain (`ZK/HopsPatch.lean`, `zk_roP`): the H6 hop pays
  `(s₅ + 1)·2⁻¹²⁸` (a sibling input in `S`'s `H₅` queries is a guess of the label-row pad `Θ`), the
  H4 hop `221·s_E·2⁻¹²⁸` (a hidden GGM node in `S`'s cipher queries);
* the `H₃` patch: the prover reads its slice only at `ρ` (`realRO_g3_congr`), a uniform **16-byte**
  value independent of `S`'s queries: `s₃·2⁻¹²⁸`;
* the `H₂³` patch: the prover reads `H₂³` only at its grinding prefix's block
  (`realRO_progAt`), and the simulator programs only the block of the prefix recomputed from its
  proof (`progRO_progAt`). The simulated block's tail is the simulator's uniform `ã`
  (`16·(d − 1)` bytes) or a constant if it produced no proof, so it is one of `S`'s `≤ s₂` queried
  blocks with probability `≤ noHitProb + s₂·2^(−8·16(d−1))`; the real prover's block, by a second
  application of zero knowledge (`pr_preBlk_mem`, as `pr_collide_zk`: unless the grinding outcome
  is bad, the block is the one recomputed from the proof, a distinguisher reading `H₅` and the
  cipher at `312`, `4607` keys), with probability `≤ 2⁻¹¹⁰ + εROP(0, 312, 4607) + noHitProb +
  s₂·2^(−8·16(d−1))`. Without `H₂³` reads (`s₂ = 0`) the term vanishes.

**`zk_adaptive`**: the advantage is at most

    εAd = εRO(q₃, q₅, q_E) + (221·s_E + s₅ + 1)·2⁻¹²⁸ + s₃·2⁻¹²⁸
          + [s₂ > 0]·(2⁻¹¹⁰ + εRO(0, 312, 4607) + (221·s_E + s₅ + 1)·2⁻¹²⁸
                      + 2·noHitProb + 2·s₂·2^(−8·16(d−1))).

Everything but `zk_roP` is stated for any type of cipher rows (`ShG R p`, `Tb R p`) with
**`ZKPRow R`**, the class of row types with `zk_roP` (an error `εP p q₃ q₅ q_E |P5| |PE|`;
`εAdG`, `h23G` the errors above with it). Instances: `ZKPRow.fn` (`εROP`; `εAdG (Blk → Blk) p =
εAd`) and `ZKPRow.perm` (`εROPmP`, `ZK/HopsPatchPerm.lean`; `εAdG (Equiv.Perm Blk) p = εAdPm p`).

For `d = 9` the `H₂³` term is about `2⁻¹⁰⁶·²` (the second zero-knowledge error) plus
`2·s₂·2⁻¹⁰²⁴`: the price of `S` reading `H₂³` is a second application of the theorem, not a
function of `s₂` beyond the `2⁻¹⁰²⁴`.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

set_option linter.unusedSectionVars false

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy
open VoleMole.ZK.IC (patchT patchT_of_mem patchT_of_not_mem patchT_programAt)

/-! ## The patched tables and their reads -/

section Patch

variable {R : Type} {p : Params}

/-- The shared tables with `H₅` patched on `P5` and the cipher on `PE`. -/
def patch5E (P5 : Finset (Bytes 37)) (W5 : Tab5F) (PE : Finset Blk) (WE : Blk → R) (s : ShG R p) :
    ShG R p :=
  (s.1, patchT P5 W5 s.2.1, patchT PE WE s.2.2)

/-- The shared tables with `H₂³` patched on `P2`. -/
def patch2 (P2 : Finset (K2 p)) (W2 : Tab2G p) (s : ShG R p) : ShG R p := (patchT P2 W2 s.1, s.2)

/-- **The `H₂³` patch is a programming at the patched keys' blocks.** -/
lemma patch2_progAt (P2 : Finset (K2 p)) (W2 : Tab2G p) :
    ProgAt (patch2 (R := R) P2 W2) (fun _ => P2.image Prod.fst) := by
  classical
  refine ⟨fun _ => rfl, fun s k hk => ?_⟩
  refine patchT_of_not_mem _ _ fun h => hk ?_
  exact Finset.mem_image.2 ⟨k, h, rfl⟩

variable {O : Type*} {q3 q5 qE : ℕ}

/-- **A distinguisher of the patched tables has the budget of the distinguisher.** -/
lemma Budget.of_patch {D : O → Tab3 → ShG R p → Prop} (hD : Budget p q3 q5 qE D) (P3 : Finset (Bytes 16))
    (W3 : Tab3) (P2 : Finset (K2 p)) (W2 : Tab2G p) :
    Budget p q3 q5 qE (fun o g s => D o (patchT P3 W3 g) (patch2 P2 W2 s)) := by
  refine ⟨fun o s => ?_, fun o g => ?_, fun o g => ?_⟩
  · obtain ⟨Q, hQ, hf⟩ := hD.h3 o (patch2 P2 W2 s)
    refine ⟨fun g => Q (patchT P3 W3 g), fun g => hQ _, fun g g' h => ?_⟩
    refine hf _ _ fun k hk => ?_
    by_cases hk3 : k ∈ P3
    · rw [patchT_of_mem _ _ hk3, patchT_of_mem _ _ hk3]
    · rw [patchT_of_not_mem _ _ hk3, patchT_of_not_mem _ _ hk3]
      exact h k hk
  · obtain ⟨Q, hQ, hf⟩ := hD.h5 o (patchT P3 W3 g)
    exact ⟨fun s => Q (patch2 P2 W2 s), fun s => hQ _, fun s G5 h => hf (patch2 P2 W2 s) G5 h⟩
  · obtain ⟨Q, hQ, hf⟩ := hD.hE o (patchT P3 W3 g)
    exact ⟨fun s => Q (patch2 P2 W2 s), fun s => hQ _, fun s E h => hf (patch2 P2 W2 s) E h⟩

/-- **A distinguisher of the `H₅`-and-cipher-patched tables has the budget of the
distinguisher.** -/
lemma Budget.of_patch5E {D : O → Tab3 → ShG R p → Prop} (hD : Budget p q3 q5 qE D)
    (P5 : Finset (Bytes 37)) (W5 : Tab5F) (PE : Finset Blk) (WE : Blk → R) :
    Budget p q3 q5 qE (fun o g s => D o g (patch5E P5 W5 PE WE s)) := by
  refine ⟨fun o s => hD.h3 o _, fun o g => ?_, fun o g => ?_⟩
  · obtain ⟨Q, hQ, hf⟩ := hD.h5 o g
    refine ⟨fun s => Q (patch5E P5 W5 PE WE s), fun s => hQ _, fun s G5 h => ?_⟩
    refine hf (patch5E P5 W5 PE WE s) (patchT P5 W5 G5) fun k hk => ?_
    by_cases hk5 : k ∈ P5
    · show patchT P5 W5 s.2.1 k = patchT P5 W5 G5 k
      rw [patchT_of_mem _ _ hk5, patchT_of_mem _ _ hk5]
    · show patchT P5 W5 s.2.1 k = patchT P5 W5 G5 k
      rw [patchT_of_not_mem _ _ hk5, patchT_of_not_mem _ _ hk5]
      exact h k hk
  · obtain ⟨Q, hQ, hf⟩ := hD.hE o g
    refine ⟨fun s => Q (patch5E P5 W5 PE WE s), fun s => hQ _, fun s E h => ?_⟩
    refine hf (patch5E P5 W5 PE WE s) (patchT PE WE E) fun k hk => ?_
    by_cases hkE : k ∈ PE
    · show patchT PE WE s.2.2 k = patchT PE WE E k
      rw [patchT_of_mem _ _ hkE, patchT_of_mem _ _ hkE]
    · show patchT PE WE s.2.2 k = patchT PE WE E k
      rw [patchT_of_not_mem _ _ hkE, patchT_of_not_mem _ _ hkE]
      exact h k hk

end Patch

/-! ## Zero knowledge with `H₅` and the cipher patched -/

section ZKP

/-- **The error of `zk_roP`**: `εRO` plus the patches' terms. -/
noncomputable def εROP (q3 q5 qE n5 nE : ℕ) : ℝ :=
  εRO q3 q5 qE + 221 * nE / 2 ^ 128 + (n5 + 1) / 2 ^ 128

lemma εROP_nonneg (q3 q5 qE n5 nE : ℕ) : 0 ≤ εROP q3 q5 qE n5 nE := by
  unfold εROP; have := εRO_nonneg' q3 q5 qE; positivity

lemma εROP_mono {q3 q5 qE n5 nE q3' q5' qE' n5' nE' : ℕ} (h3 : q3 ≤ q3') (h5 : q5 ≤ q5')
    (hE : qE ≤ qE') (h5' : n5 ≤ n5') (hE' : nE ≤ nE') :
    εROP q3 q5 qE n5 nE ≤ εROP q3' q5' qE' n5' nE' := by
  unfold εROP
  have := εRO_mono h3 h5 hE
  have a : (n5 : ℝ) ≤ n5' := by exact_mod_cast h5'
  have b : (nE : ℝ) ≤ nE' := by exact_mod_cast hE'
  gcongr

variable (Hb : Hashes) (st : Statement) (w : ByteArray)

/-- **Zero knowledge with the `H₅` table patched on `P5` and the cipher on `PE`** (`zk_ro` from
`zk_rom_ic_h23P_num`): the prover, the simulator's programming and the distinguisher see the
patched tables. -/
theorem zk_roP {cs : ByteArray → ByteArray → System GF128} (hlr : st.params.labelRows = true)
    (hzk : ZKHyp CrtGen.tables st w cs) (hHb : HashesWF Hb) (hp : SmallParams st.params)
    {q3 q5 qE : ℕ} (D : Except String ByteArray → Tab3 → Sh st.params → Prop)
    (hD : Budget st.params q3 q5 qE D) (P5 : Finset (Bytes 37)) (W5 : Tab5F) (PE : Finset Blk)
    (WE : Cipher) :
    |pr ((Bytes 16 × Tab3) × Sh st.params) (fun a =>
        D (realRO st.params Hb st w a.1.1 a.1.2 (patch5E P5 W5 PE WE a.2)) a.1.2
          (patch5E P5 W5 PE WE a.2)) -
      pr ((SimCoins st.params × Tab3) × Sh st.params) (fun a =>
        D (simulate st.params a.1.1) a.1.2
          (progRO st.params Hb st a.1.1 (patch5E P5 W5 PE WE a.2)))| ≤
      εROP q3 q5 qE P5.card PE.card := by
  choose Q3 hQ3c hQ3 using hD.h3
  choose Q5 hQ5c hQ5 using hD.h5
  choose QE hQEc hQE using hD.hE
  have key := zk_rom_ic_h23P_num Hb st w hlr hzk hHb hp (fun o G3 G2 G5 E => D o G3 (G2, G5, E))
    (fun o G3 G2 G5 E => Q3 o (G2, G5, E) G3)
    (fun o G3 G3' G2 G5 E hk => Iff.of_eq (hQ3 o (G2, G5, E) G3 G3' hk).symm)
    (fun o G3 G2 G5 E => hQ3c o (G2, G5, E) G3)
    (fun o G3 G2 G5 E => Q5 o G3 (G2, G5, E))
    (fun o G3 G2 G5 G5' E hk => Iff.of_eq (hQ5 o G3 (G2, G5, E) G5' hk).symm)
    (fun o G3 G2 G5 E => hQ5c o G3 (G2, G5, E))
    (fun o G3 G2 G5 E => QE o G3 (G2, G5, E))
    (fun o G3 G2 G5 E E' hk => Iff.of_eq (hQE o G3 (G2, G5, E) E' hk).symm)
    (fun o G3 G2 G5 E => hQEc o G3 (G2, G5, E)) P5 W5 PE WE
  let e1 : ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × Cipher ≃
      (Bytes 16 × Tab3) × Sh st.params :=
    { toFun := fun c => ((c.1.1.1, c.1.2.1), (c.1.1.2, c.1.2.2, c.2))
      invFun := fun c => (((c.1.1, c.2.1), (c.1.2, c.2.2.1)), c.2.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e2 : (SimCoins st.params × Vis2 st.params) × Cipher ≃
      (SimCoins st.params × Tab3) × Sh st.params :=
    { toFun := fun c => ((c.1.1, c.1.2.1), (c.1.2.2.1, c.1.2.2.2, c.2))
      invFun := fun c => ((c.1.1, (c.1.2, c.2.1, c.2.2.1)), c.2.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e1, ← pr_equiv e2]
  refine key.trans (le_of_eq ?_)
  unfold εROP εRO
  ring

/-- **Zero knowledge with `H₅` and the cipher patched, for a type of cipher rows** (`zk_roP` with
the cipher's rows in `R`): an error `εP p q₃ q₅ q_E |P5| |PE|`, monotone and nonnegative. Function
rows: `εROP` (`zk_roP`, `ZKPRow.fn`). The adaptive-statement theorems below and the games with a
table-reading adversary are stated for every row type with this structure. -/
class ZKPRow (R : Type) [Fintype R] [CipherRow R] where
  /-- The error with the `H₅` and cipher tables patched on `n5`, `nE` keys. -/
  εP : Params → ℕ → ℕ → ℕ → ℕ → ℕ → ℝ
  εP_nonneg : ∀ p q3 q5 qE n5 nE, 0 ≤ εP p q3 q5 qE n5 nE
  εP_mono : ∀ (p : Params) {q3 q5 qE n5 nE q3' q5' qE' n5' nE' : ℕ}, q3 ≤ q3' → q5 ≤ q5' →
    qE ≤ qE' → n5 ≤ n5' → nE ≤ nE' → εP p q3 q5 qE n5 nE ≤ εP p q3' q5' qE' n5' nE'
  /-- `zk_roP` with this row type. -/
  zkP : ∀ (Hb : Hashes) (st : Statement) (w : ByteArray) {cs : ByteArray → ByteArray → System GF128},
    st.params.labelRows = true → ZKHyp CrtGen.tables st w cs → HashesWF Hb →
    SmallParams st.params → ∀ {q3 q5 qE : ℕ} (D : Except String ByteArray → Tab3 →
      ShG R st.params → Prop), Budget st.params q3 q5 qE D →
    ∀ (P5 : Finset (Bytes 37)) (W5 : Tab5F) (PE : Finset Blk) (WE : Blk → R),
    |pr ((Bytes 16 × Tab3) × ShG R st.params) (fun a =>
        D (realRO st.params Hb st w a.1.1 a.1.2 (patch5E P5 W5 PE WE a.2)) a.1.2
          (patch5E P5 W5 PE WE a.2)) -
      pr ((SimCoins st.params × Tab3) × ShG R st.params) (fun a =>
        D (simulate st.params a.1.1) a.1.2
          (progRO st.params Hb st a.1.1 (patch5E P5 W5 PE WE a.2)))| ≤
      εP st.params q3 q5 qE P5.card PE.card

/-- **Function rows**: `zk_roP`, error `εROP`. -/
noncomputable instance ZKPRow.fn : ZKPRow (Blk → Blk) where
  εP _ := εROP
  εP_nonneg _ := εROP_nonneg
  εP_mono _ _ _ _ _ _ _ _ _ _ _ h3 h5 hE h5' hE' := εROP_mono h3 h5 hE h5' hE'
  zkP Hb st w _ hlr hzk hHb hp _ _ _ D hD P5 W5 PE WE :=
    zk_roP Hb st w hlr hzk hHb hp D hD P5 W5 PE WE

@[simp] lemma ZKPRow.εP_fn (p : Params) : ZKPRow.εP (Blk → Blk) p = εROP := rfl

end ZKP

/-! ## The `H₃` and `H₂³` patches, for a fixed statement -/

section Fixed

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R]
variable {Hb : Hashes} {st : Statement} {w : ByteArray} {cs : ByteArray → ByteArray → System GF128}

/-- **The real prover reads its `H₃` slice only at its randomness `ρ`.** -/
theorem realRO_g3_congr (hzk : ZKHyp CrtGen.tables st w cs) (hHb : HashesWF Hb)
    (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows) (ρ : Bytes 16)
    {G3 G3' : Tab3} (s : ShG R st.params) (h : G3 ρ = G3' ρ) :
    realRO st.params Hb st w ρ G3 s = realRO st.params Hb st w ρ G3' s := by
  rw [realRO_eq, realRO_eq, @prove_recH_eq (icPrg (rowFn s.2.2)) Hb st w cs hzk hHb hlab,
    @prove_recH_eq (icPrg (rowFn s.2.2)) Hb st w cs hzk hHb hlab, h]
  have hag : (recB Hb st w G3 s.2.1).AgreeOff .h3 (recB Hb st w G3' s.2.1) :=
    @recH_agreeOff_h3 (icPrg (rowFn s.2.2)) Hb st w G3 G3' (fun _ => 0) s.2.1
  rw [@hyb3_agreeOff (icPrg (rowFn s.2.2)) _ _ _ unread_h3 hag]

/-- The grinding answers at the real prover's prefix are uniform, with `H₅` and the cipher
patched. -/
theorem pr_grindBad_preRO5E (P5 : Finset (Bytes 37)) (W5 : Tab5F) (PE : Finset Blk) (WE : Blk → R) :
    pr ((Bytes 16 × Tab3) × ShG R st.params) (fun a =>
      GrindBad CrtGen.tables (a.2.1 ∘ key2 st.params
        (preRO Hb st w a.1.1 a.1.2 (patch5E P5 W5 PE WE a.2)))) ≤ 1 / 2 ^ 110 := by
  refine pr_le_of_fst fun x => pr_le_of_snd fun r => ?_
  have h := close_restrict (R := Bytes 16)
    (key2_injective st.params (@preR (icPrg (rowFn (patchT PE WE r.2))) Hb CrtGen.tables st w
      (patchT P5 W5 r.1) (splitSeed (x.2 x.1))))
    (GrindBad CrtGen.tables)
  rw [abs_nonpos_iff, sub_eq_zero] at h
  exact (le_of_eq h).trans grindBad_le_110

/-- **A simulated proof's programmed block is in a fixed set** `B` with probability
`≤ noHitProb + |B|·2^(−8·16(d−1))`, for every table. -/
theorem pr_simBlk_mem (hHb : HashesWF Hb) (s : ShG R st.params) (B : Finset (Bytes (preLen st.params))) :
    pr (SimCoins st.params) (fun c => simBlk Hb st c s ∈ B) ≤
      noHitProb + B.card / 2 ^ (8 * (16 * (st.params.qsDegree - 1))) := by
  classical
  refine (pr_mono (Q := fun c => simTail c ∈ B.image preTail) fun c hc => ?_).trans
    ((pr_simTail_mem _).trans ?_)
  · rw [← preTail_simBlk hHb rfl c s]
    exact Finset.mem_image_of_mem _ hc
  · have : ((B.image preTail).card : ℝ) ≤ B.card := by exact_mod_cast Finset.card_image_le
    gcongr

/-- **The tail of the real prover's grinding block is in a fixed set** `T`, with `H₅` and the
cipher patched, with probability `≤ 2⁻¹¹⁰ + εROP(0, 312, 4607) + noHitProb + |T|·2^(−8·16(d−1))`:
unless the grinding outcome is bad, it is the block recomputed from the proof (`realRO_vPre`); by
zero knowledge (`zk_roP`) the recomputed tail is in `T` with the simulated proof's probability, and
the simulated tail is uniform. -/
theorem pr_preTail_mem [ZKPRow R] (hlr : st.params.labelRows = true) (hzk : ZKHyp CrtGen.tables st w cs)
    (hHb : HashesWF Hb) (hp : SmallParams st.params) (P5 : Finset (Bytes 37)) (W5 : Tab5F)
    (PE : Finset Blk) (WE : Blk → R) (T : Finset ByteArray) :
    pr ((Bytes 16 × Tab3) × ShG R st.params) (fun a =>
        preTail (blk (preLen st.params) (preRO Hb st w a.1.1 a.1.2 (patch5E P5 W5 PE WE a.2))) ∈ T) ≤
      1 / 2 ^ 110 + ZKPRow.εP R st.params 0 312 4607 P5.card PE.card +
        (noHitProb + T.card / 2 ^ (8 * (16 * (st.params.qsDegree - 1)))) := by
  classical
  obtain ⟨hl1, -, -, hl2⟩ := labelRows_sizes hlr
  have hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows := by omega
  let D : Except String ByteArray → Tab3 → ShG R st.params → Prop := fun o _ s => TailIn Hb st T o s
  have hD : Budget st.params 0 312 4607 D :=
    ⟨fun o s => Rd3.const (TailIn Hb st T o s),
      fun o _ => (outPre_rd5 Hb st o).map fun P => preTail (blk (preLen st.params) P) ∈ T,
      fun o _ => (outPre_rdE Hb st o).map fun P => preTail (blk (preLen st.params) P) ∈ T⟩
  have hsplit : ∀ a : (Bytes 16 × Tab3) × ShG R st.params,
      preTail (blk (preLen st.params) (preRO Hb st w a.1.1 a.1.2 (patch5E P5 W5 PE WE a.2))) ∈ T →
      GrindBad CrtGen.tables (a.2.1 ∘ key2 st.params
          (preRO Hb st w a.1.1 a.1.2 (patch5E P5 W5 PE WE a.2))) ∨
        D (realRO st.params Hb st w a.1.1 a.1.2 (patch5E P5 W5 PE WE a.2)) a.1.2
          (patch5E P5 W5 PE WE a.2) := by
    intro a h
    by_cases hg : GrindBad CrtGen.tables (a.2.1 ∘ key2 st.params
        (preRO Hb st w a.1.1 a.1.2 (patch5E P5 W5 PE WE a.2)))
    · exact Or.inl hg
    · right
      obtain ⟨proof, hok, hv⟩ := realRO_vPre hzk hHb hlab a.1.1 a.1.2 (patch5E P5 W5 PE WE a.2) hg
      show preTail (blk (preLen st.params)
        (@outPre (icPrg (rowFn (patch5E P5 W5 PE WE a.2).2.2)) Hb CrtGen.tables st
          (patch5E P5 W5 PE WE a.2).2.1
          (realRO st.params Hb st w a.1.1 a.1.2 (patch5E P5 W5 PE WE a.2)))) ∈ T
      rw [hok, hv]
      exact h
  have hz := ZKPRow.zkP Hb st w hlr hzk hHb hp D hD P5 W5 PE WE
  have hsim : pr ((SimCoins st.params × Tab3) × ShG R st.params) (fun a =>
      D (simulate st.params a.1.1) a.1.2 (progRO st.params Hb st a.1.1 (patch5E P5 W5 PE WE a.2))) ≤
      noHitProb + T.card / 2 ^ (8 * (16 * (st.params.qsDegree - 1))) := by
    have e : ∀ a : (SimCoins st.params × Tab3) × ShG R st.params,
        D (simulate st.params a.1.1) a.1.2 (progRO st.params Hb st a.1.1 (patch5E P5 W5 PE WE a.2)) ↔
          simTail a.1.1 ∈ T := fun a => by
      show preTail (blk (preLen st.params)
        (@outPre (icPrg (rowFn (patchT PE WE a.2.2.2))) Hb CrtGen.tables st (patchT P5 W5 a.2.2.1)
          (simulate st.params a.1.1))) ∈ T ↔ _
      rw [@preTail_outPre st.params (icPrg (rowFn (patchT PE WE a.2.2.2))) Hb hHb CrtGen.tables st rfl
        (patchT P5 W5 a.2.2.1) a.1.1]
    rw [pr_congr e]
    have e1 := pr_prod_fst (β := ShG R st.params)
      (fun c : SimCoins st.params × Tab3 => simTail c.1 ∈ T)
    have e2 := pr_prod_fst (β := Tab3) (fun c : SimCoins st.params => simTail c ∈ T)
    exact (e1.trans e2).le.trans (pr_simTail_mem T)
  have hreal : pr ((Bytes 16 × Tab3) × ShG R st.params) (fun a =>
      D (realRO st.params Hb st w a.1.1 a.1.2 (patch5E P5 W5 PE WE a.2)) a.1.2
        (patch5E P5 W5 PE WE a.2)) ≤
      ZKPRow.εP R st.params 0 312 4607 P5.card PE.card +
        (noHitProb + T.card / 2 ^ (8 * (16 * (st.params.qsDegree - 1)))) := by
    have := (abs_sub_le_iff.1 hz).1
    linarith
  refine (pr_mono hsplit).trans ((pr_or_le _ _).trans ?_)
  have := pr_grindBad_preRO5E (R := R) (Hb := Hb) (st := st) (w := w) P5 W5 PE WE
  linarith

/-- **The real prover's grinding block is in a fixed set** `B` (`pr_preTail_mem` for `B`'s
tails). -/
theorem pr_preBlk_mem [ZKPRow R] (hlr : st.params.labelRows = true) (hzk : ZKHyp CrtGen.tables st w cs)
    (hHb : HashesWF Hb) (hp : SmallParams st.params) (P5 : Finset (Bytes 37)) (W5 : Tab5F)
    (PE : Finset Blk) (WE : Blk → R) (B : Finset (Bytes (preLen st.params))) :
    pr ((Bytes 16 × Tab3) × ShG R st.params) (fun a =>
        blk (preLen st.params) (preRO Hb st w a.1.1 a.1.2 (patch5E P5 W5 PE WE a.2)) ∈ B) ≤
      1 / 2 ^ 110 + ZKPRow.εP R st.params 0 312 4607 P5.card PE.card +
        (noHitProb + B.card / 2 ^ (8 * (16 * (st.params.qsDegree - 1)))) := by
  classical
  refine (pr_mono fun a h => Finset.mem_image_of_mem preTail h).trans
    ((pr_preTail_mem hlr hzk hHb hp P5 W5 PE WE (B.image preTail)).trans ?_)
  have : ((B.image preTail).card : ℝ) ≤ B.card := by exact_mod_cast Finset.card_image_le
  gcongr

/-- **The `H₂³` patch commutes with a simulation that programs another block.** -/
lemma progRO_patch2 {p : Params} (c : SimCoins p) (s : ShG R p) (P2 : Finset (K2 p)) (W2 : Tab2G p)
    (h : simBlk Hb st c s ∉ P2.image Prod.fst) :
    progRO p Hb st c (patch2 P2 W2 s) = patch2 P2 W2 (progRO p Hb st c s) := by
  classical
  refine Prod.ext ?_ rfl
  show programAt (key2 p (@outPre (icPrg (rowFn s.2.2)) Hb CrtGen.tables st s.2.1 (simulate p c))) c.1.2.1
      (patchT P2 W2 s.1) =
    patchT P2 W2 (programAt (key2 p (@outPre (icPrg (rowFn s.2.2)) Hb CrtGen.tables st s.2.1
      (simulate p c))) c.1.2.1 s.1)
  refine (patchT_programAt W2 c.1.2.1 s.1 fun i hi => h ?_).symm
  exact Finset.mem_image.2 ⟨_, hi, rfl⟩

/-- **The `H₂³` term**: zero without `H₂³` patch; else the real prover's block and the simulated
block in the patched blocks. -/
noncomputable def h23Term (d n5 nE n2 : ℕ) : ℝ :=
  if n2 = 0 then 0 else
    1 / 2 ^ 110 + εROP 0 312 4607 n5 nE + 2 * (noHitProb + n2 / 2 ^ (8 * (16 * (d - 1))))

lemma h23Term_nonneg (d n5 nE n2 : ℕ) : 0 ≤ h23Term d n5 nE n2 := by
  unfold h23Term
  split_ifs
  · exact le_rfl
  · have := εROP_nonneg 0 312 4607 n5 nE
    have : 0 ≤ noHitProb := pr_nonneg _
    positivity

lemma h23Term_mono {d n5 nE n2 n5' nE' n2' : ℕ} (h5 : n5 ≤ n5') (hE : nE ≤ nE') (h2 : n2 ≤ n2') :
    h23Term d n5 nE n2 ≤ h23Term d n5' nE' n2' := by
  unfold h23Term
  split_ifs with ha hb
  · exact le_rfl
  · have := εROP_nonneg 0 312 4607 n5' nE'
    have : 0 ≤ noHitProb := pr_nonneg _
    positivity
  · omega
  · have := εROP_mono (le_refl 0) (le_refl 312) (le_refl 4607) h5 hE
    have : (n2 : ℝ) ≤ n2' := by exact_mod_cast h2
    gcongr

/-- **The `H₂³` term for a type of cipher rows** (`h23Term` with `ZKPRow.εP`). -/
noncomputable def h23G (R : Type) [Fintype R] [CipherRow R] [ZKPRow R] (p : Params)
    (d n5 nE n2 : ℕ) : ℝ :=
  if n2 = 0 then 0 else
    1 / 2 ^ 110 + ZKPRow.εP R p 0 312 4607 n5 nE + 2 * (noHitProb + n2 / 2 ^ (8 * (16 * (d - 1))))

@[simp] lemma h23G_fn (p : Params) : h23G (Blk → Blk) p = h23Term := rfl

lemma h23G_nonneg [ZKPRow R] (p : Params) (d n5 nE n2 : ℕ) : 0 ≤ h23G R p d n5 nE n2 := by
  unfold h23G
  split_ifs
  · exact le_rfl
  · have := ZKPRow.εP_nonneg (R := R) p 0 312 4607 n5 nE
    have : 0 ≤ noHitProb := pr_nonneg _
    positivity

lemma h23G_mono [ZKPRow R] (p : Params) {d n5 nE n2 n5' nE' n2' : ℕ} (h5 : n5 ≤ n5')
    (hE : nE ≤ nE') (h2 : n2 ≤ n2') : h23G R p d n5 nE n2 ≤ h23G R p d n5' nE' n2' := by
  unfold h23G
  split_ifs with ha hb
  · exact le_rfl
  · have := ZKPRow.εP_nonneg (R := R) p 0 312 4607 n5' nE'
    have : 0 ≤ noHitProb := pr_nonneg _
    positivity
  · omega
  · have := ZKPRow.εP_mono (R := R) p (le_refl 0) (le_refl 312) (le_refl 4607) h5 hE
    have : (n2 : ℝ) ≤ n2' := by exact_mod_cast h2
    gcongr

variable (Hb st w)

/-- **Zero knowledge with all four tables patched** (fixed statement): the `H₃` slice on `P3`,
`H₂³` on `P2`, `H₅` on `P5`, the cipher on `PE`; the prover, the simulator's programming and the
distinguisher see the patched tables. -/
theorem zk_patched [ZKPRow R] (hlr : st.params.labelRows = true) (hzk : ZKHyp CrtGen.tables st w cs)
    (hHb : HashesWF Hb) (hp : SmallParams st.params) {q3 q5 qE : ℕ}
    (D : Except String ByteArray → Tab3 → ShG R st.params → Prop) (hD : Budget st.params q3 q5 qE D)
    (P3 : Finset (Bytes 16)) (W3 : Tab3) (P2 : Finset (K2 st.params)) (W2 : Tab2G st.params)
    (P5 : Finset (Bytes 37)) (W5 : Tab5F) (PE : Finset Blk) (WE : Blk → R) :
    |pr ((Bytes 16 × Tab3) × ShG R st.params) (fun a =>
        D (realRO st.params Hb st w a.1.1 (patchT P3 W3 a.1.2)
            (patch2 P2 W2 (patch5E P5 W5 PE WE a.2)))
          (patchT P3 W3 a.1.2) (patch2 P2 W2 (patch5E P5 W5 PE WE a.2))) -
      pr ((SimCoins st.params × Tab3) × ShG R st.params) (fun a =>
        D (simulate st.params a.1.1) (patchT P3 W3 a.1.2)
          (progRO st.params Hb st a.1.1 (patch2 P2 W2 (patch5E P5 W5 PE WE a.2))))| ≤
      ZKPRow.εP R st.params q3 q5 qE P5.card PE.card + P3.card / 2 ^ 128 +
        h23G R st.params st.params.qsDegree P5.card PE.card P2.card := by
  classical
  obtain ⟨hl1, -, -, hl2⟩ := labelRows_sizes hlr
  have hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows := by omega
  let B2 := P2.image Prod.fst
  let D' : Except String ByteArray → Tab3 → ShG R st.params → Prop :=
    fun o g s => D o (patchT P3 W3 g) (patch2 P2 W2 s)
  have hD' : Budget st.params q3 q5 qE D' := hD.of_patch P3 W3 P2 W2
  have hz := ZKPRow.zkP Hb st w hlr hzk hHb hp D' hD' P5 W5 PE WE
  have hR : |pr ((Bytes 16 × Tab3) × ShG R st.params) (fun a =>
        D (realRO st.params Hb st w a.1.1 (patchT P3 W3 a.1.2)
            (patch2 P2 W2 (patch5E P5 W5 PE WE a.2)))
          (patchT P3 W3 a.1.2) (patch2 P2 W2 (patch5E P5 W5 PE WE a.2))) -
      pr ((Bytes 16 × Tab3) × ShG R st.params) (fun a =>
        D' (realRO st.params Hb st w a.1.1 a.1.2 (patch5E P5 W5 PE WE a.2)) a.1.2
          (patch5E P5 W5 PE WE a.2))| ≤
      pr ((Bytes 16 × Tab3) × ShG R st.params) (fun a => a.1.1 ∈ P3 ∨
        blk (preLen st.params) (preRO Hb st w a.1.1 a.1.2 (patch5E P5 W5 PE WE a.2)) ∈ B2) := by
    refine abs_pr_sub_le_of_agree _ _ _ fun a ha => ?_
    push Not at ha
    have h1 : realRO st.params Hb st w a.1.1 (patchT P3 W3 a.1.2)
        (patch2 P2 W2 (patch5E P5 W5 PE WE a.2)) =
        realRO st.params Hb st w a.1.1 a.1.2 (patch2 P2 W2 (patch5E P5 W5 PE WE a.2)) :=
      realRO_g3_congr hzk hHb hlab a.1.1 _ (patchT_of_not_mem _ _ ha.1)
    have h2 : realRO st.params Hb st w a.1.1 a.1.2 (patch2 P2 W2 (patch5E P5 W5 PE WE a.2)) =
        realRO st.params Hb st w a.1.1 a.1.2 (patch5E P5 W5 PE WE a.2) :=
      realRO_progAt hzk hHb hlab (patch2_progAt P2 W2) a.1.1 a.1.2 _ ha.2
    show D _ _ _ ↔ D _ _ _
    rw [h1, h2]
  have hS : |pr ((SimCoins st.params × Tab3) × ShG R st.params) (fun a =>
        D (simulate st.params a.1.1) (patchT P3 W3 a.1.2)
          (progRO st.params Hb st a.1.1 (patch2 P2 W2 (patch5E P5 W5 PE WE a.2)))) -
      pr ((SimCoins st.params × Tab3) × ShG R st.params) (fun a =>
        D' (simulate st.params a.1.1) a.1.2
          (progRO st.params Hb st a.1.1 (patch5E P5 W5 PE WE a.2)))| ≤
      pr ((SimCoins st.params × Tab3) × ShG R st.params) (fun a =>
        simBlk Hb st a.1.1 (patch5E P5 W5 PE WE a.2) ∈ B2) := by
    refine abs_pr_sub_le_of_agree _ _ _ fun a ha => ?_
    show D _ _ _ ↔ D _ _ _
    rw [progRO_patch2 a.1.1 _ P2 W2 ha]
  -- The probabilities.
  have hρ : pr ((Bytes 16 × Tab3) × ShG R st.params) (fun a => a.1.1 ∈ P3) ≤ P3.card / 2 ^ 128 := by
    rw [pr_prod_fst (β := ShG R st.params) (fun c : Bytes 16 × Tab3 => c.1 ∈ P3),
      pr_prod_fst (β := Tab3) (fun r : Bytes 16 => r ∈ P3)]
    have := pr_mem_le (α := Bytes 16) id Function.injective_id P3
    rw [card_bytes16] at this
    exact this.trans (le_of_eq (by norm_num))
  have h23 : pr ((Bytes 16 × Tab3) × ShG R st.params) (fun a =>
        blk (preLen st.params) (preRO Hb st w a.1.1 a.1.2 (patch5E P5 W5 PE WE a.2)) ∈ B2) +
      pr ((SimCoins st.params × Tab3) × ShG R st.params) (fun a =>
        simBlk Hb st a.1.1 (patch5E P5 W5 PE WE a.2) ∈ B2) ≤
      h23G R st.params st.params.qsDegree P5.card PE.card P2.card := by
    unfold h23G
    split_ifs with h0
    · have hB : B2 = ∅ := by
        rw [Finset.card_eq_zero] at h0
        simp only [B2, h0, Finset.image_empty]
      simp only [hB, Finset.notMem_empty, pr_false, add_zero, le_refl]
    · have hc : (B2.card : ℝ) ≤ P2.card := by exact_mod_cast Finset.card_image_le
      have h1 := pr_preBlk_mem hlr hzk hHb hp P5 W5 PE WE B2
      have h2 : pr ((SimCoins st.params × Tab3) × ShG R st.params) (fun a =>
          simBlk Hb st a.1.1 (patch5E P5 W5 PE WE a.2) ∈ B2) ≤
          noHitProb + B2.card / 2 ^ (8 * (16 * (st.params.qsDegree - 1))) :=
        pr_le_of_snd fun s => by
          rw [pr_prod_fst (β := Tab3) (fun c : SimCoins st.params =>
            simBlk Hb st c (patch5E P5 W5 PE WE s) ∈ B2)]
          exact pr_simBlk_mem hHb _ B2
      have h3 : (B2.card : ℝ) / 2 ^ (8 * (16 * (st.params.qsDegree - 1))) ≤
          P2.card / 2 ^ (8 * (16 * (st.params.qsDegree - 1))) := by gcongr
      linarith
  have hor := pr_or_le (fun a : (Bytes 16 × Tab3) × ShG R st.params => a.1.1 ∈ P3)
    (fun a => blk (preLen st.params) (preRO Hb st w a.1.1 a.1.2 (patch5E P5 W5 PE WE a.2)) ∈ B2)
  have t1 := abs_sub_le
    (pr ((Bytes 16 × Tab3) × ShG R st.params) (fun a =>
        D (realRO st.params Hb st w a.1.1 (patchT P3 W3 a.1.2)
            (patch2 P2 W2 (patch5E P5 W5 PE WE a.2)))
          (patchT P3 W3 a.1.2) (patch2 P2 W2 (patch5E P5 W5 PE WE a.2))))
    (pr ((Bytes 16 × Tab3) × ShG R st.params) (fun a =>
        D' (realRO st.params Hb st w a.1.1 a.1.2 (patch5E P5 W5 PE WE a.2)) a.1.2
          (patch5E P5 W5 PE WE a.2)))
    (pr ((SimCoins st.params × Tab3) × ShG R st.params) (fun a =>
        D (simulate st.params a.1.1) (patchT P3 W3 a.1.2)
          (progRO st.params Hb st a.1.1 (patch2 P2 W2 (patch5E P5 W5 PE WE a.2)))))
  have t2 := abs_sub_le
    (pr ((Bytes 16 × Tab3) × ShG R st.params) (fun a =>
        D' (realRO st.params Hb st w a.1.1 a.1.2 (patch5E P5 W5 PE WE a.2)) a.1.2
          (patch5E P5 W5 PE WE a.2)))
    (pr ((SimCoins st.params × Tab3) × ShG R st.params) (fun a =>
        D' (simulate st.params a.1.1) a.1.2
          (progRO st.params Hb st a.1.1 (patch5E P5 W5 PE WE a.2))))
    (pr ((SimCoins st.params × Tab3) × ShG R st.params) (fun a =>
        D (simulate st.params a.1.1) (patchT P3 W3 a.1.2)
          (progRO st.params Hb st a.1.1 (patch2 P2 W2 (patch5E P5 W5 PE WE a.2)))))
  rw [abs_sub_comm] at hS
  linarith

end Fixed

/-! ## A statement chosen by an adversary that reads the tables -/

section Adaptive

/-- **The tables a proof sees**: its `H₃` slice and the shared tables (`H₂³`, `H₅`, cipher). -/
abbrev Tb (R : Type) (p : Params) := Tab3 × ShG R p

variable {R : Type}

/-- **Read sets** of the four tables. -/
abbrev RS (p : Params) := Finset (Bytes 16) × (Finset (K2 p) × (Finset (Bytes 37) × Finset Blk))

/-- The tables `a` on the read sets `r` and `b` elsewhere. -/
def mixT {p : Params} (r : RS p) (a b : Tb R p) : Tb R p :=
  (patchT r.1 a.1 b.1, patchT r.2.1 a.2.1 b.2.1, patchT r.2.2.1 a.2.2.1 b.2.2.1,
    patchT r.2.2.2 a.2.2.2 b.2.2.2)

/-- `a` and `a'` agree on the read sets `r`. -/
def AgT {p : Params} (r : RS p) (a a' : Tb R p) : Prop :=
  (∀ k ∈ r.1, a.1 k = a'.1 k) ∧ (∀ k ∈ r.2.1, a.2.1 k = a'.2.1 k) ∧
    (∀ k ∈ r.2.2.1, a.2.2.1 k = a'.2.2.1 k) ∧ ∀ k ∈ r.2.2.2, a.2.2.2 k = a'.2.2.2 k

lemma agT_mixT {p : Params} (r : RS p) (a b : Tb R p) : AgT r a (mixT r a b) :=
  ⟨fun _ hk => (patchT_of_mem _ _ hk).symm, fun _ hk => (patchT_of_mem _ _ hk).symm,
    fun _ hk => (patchT_of_mem _ _ hk).symm, fun _ hk => (patchT_of_mem _ _ hk).symm⟩

lemma patchT_patchT_swap {K Y : Type*} [DecidableEq K] (P : Finset K) (a b : K → Y) :
    patchT P (patchT P a b) (patchT P b a) = a :=
  funext fun k => by by_cases hk : k ∈ P <;> simp [patchT, hk]

lemma mixT_mixT {p : Params} (r : RS p) (a b : Tb R p) : mixT r (mixT r a b) (mixT r b a) = a := by
  simp only [mixT, patchT_patchT_swap]

/-- **An adversary that reads the tables**: `S`'s output depends on the tables only through the
keys `Q t` it reads (adaptively and consistently: a table that agrees with `t` on `Q t` has the same
reads and the same output), at most `s₃` keys of the `H₃` slice, `s₂` of `H₂³`, `s₅` of `H₅` and
`s_E` of the cipher. -/
def SReads {X : Type*} (p : Params) (S : Tb R p → X) (s3 s2 s5 sE : ℕ) : Prop :=
  ∃ Q : Tb R p → RS p, (∀ t t', AgT (Q t) t t' → Q t' = Q t ∧ S t' = S t) ∧
    ∀ t, (Q t).1.card ≤ s3 ∧ (Q t).2.1.card ≤ s2 ∧ (Q t).2.2.1.card ≤ s5 ∧ (Q t).2.2.2.card ≤ sE

/-- **The error of `zk_adaptive`**, for prefix degree `d`. -/
noncomputable def εAd (d q3 q5 qE s3 s2 s5 sE : ℕ) : ℝ :=
  εROP q3 q5 qE s5 sE + s3 / 2 ^ 128 + h23Term d s5 sE s2

lemma εAd_nonneg (d q3 q5 qE s3 s2 s5 sE : ℕ) : 0 ≤ εAd d q3 q5 qE s3 s2 s5 sE := by
  unfold εAd
  have := εROP_nonneg q3 q5 qE s5 sE
  have := h23Term_nonneg d s5 sE s2
  positivity

lemma εAd_mono {d q3 q5 qE s3 s2 s5 sE q3' q5' qE' s3' s2' s5' sE' : ℕ} (h3 : q3 ≤ q3')
    (h5 : q5 ≤ q5') (hE : qE ≤ qE') (i3 : s3 ≤ s3') (i2 : s2 ≤ s2') (i5 : s5 ≤ s5')
    (iE : sE ≤ sE') : εAd d q3 q5 qE s3 s2 s5 sE ≤ εAd d q3' q5' qE' s3' s2' s5' sE' := by
  unfold εAd
  have := εROP_mono h3 h5 hE i5 iE
  have := h23Term_mono (d := d) i5 iE i2
  have : (s3 : ℝ) ≤ s3' := by exact_mod_cast i3
  gcongr

/-- **The error of `zk_adaptive` for a type of cipher rows** (`εAd` with `ZKPRow.εP`). -/
noncomputable def εAdG (R : Type) [Fintype R] [CipherRow R] [ZKPRow R] (p : Params)
    (d q3 q5 qE s3 s2 s5 sE : ℕ) : ℝ :=
  ZKPRow.εP R p q3 q5 qE s5 sE + s3 / 2 ^ 128 + h23G R p d s5 sE s2

@[simp] lemma εAdG_fn (p : Params) : εAdG (Blk → Blk) p = εAd := rfl

variable [Fintype R] [Nonempty R] [CipherRow R]

lemma εAdG_nonneg [ZKPRow R] (p : Params) (d q3 q5 qE s3 s2 s5 sE : ℕ) :
    0 ≤ εAdG R p d q3 q5 qE s3 s2 s5 sE := by
  unfold εAdG
  have := ZKPRow.εP_nonneg (R := R) p q3 q5 qE s5 sE
  have := h23G_nonneg (R := R) p d s5 sE s2
  positivity

lemma εAdG_mono [ZKPRow R] (p : Params) {d q3 q5 qE s3 s2 s5 sE q3' q5' qE' s3' s2' s5' sE' : ℕ}
    (h3 : q3 ≤ q3') (h5 : q5 ≤ q5') (hE : qE ≤ qE') (i3 : s3 ≤ s3') (i2 : s2 ≤ s2') (i5 : s5 ≤ s5')
    (iE : sE ≤ sE') : εAdG R p d q3 q5 qE s3 s2 s5 sE ≤ εAdG R p d q3' q5' qE' s3' s2' s5' sE' := by
  unfold εAdG
  have := ZKPRow.εP_mono (R := R) p h3 h5 hE i5 iE
  have := h23G_mono (R := R) p (d := d) i5 iE i2
  have : (s3 : ℝ) ≤ s3' := by exact_mod_cast i3
  gcongr

variable (Hb : Hashes)

/-- The adaptive experiments for a fixed outer table `a`: a fresh table patched with `a` on `r`. -/
theorem zk_adaptive_inner [ZKPRow R] {X : Type*} (p : Params) (hlr : p.labelRows = true)
    (hsp : SmallParams p) (hHb : HashesWF Hb) (stOf : X → Statement) (wOf : X → ByteArray)
    (cs : X → ByteArray → ByteArray → System GF128) (hst : ∀ x, (stOf x).params = p)
    (hzk : ∀ x, ZKHyp CrtGen.tables (stOf x) (wOf x) (cs x)) {q3 q5 qE : ℕ}
    (D : X → Except String ByteArray → Tb R p → Prop)
    (hD : ∀ x, Budget p q3 q5 qE (fun o g s => D x o (g, s))) (x : X) (r : RS p) (a : Tb R p) :
    |pr (Bytes 16 × Tb R p) (fun z =>
        D x (realRO p Hb (stOf x) (wOf x) z.1 (mixT r a z.2).1 (mixT r a z.2).2) (mixT r a z.2)) -
      pr (SimCoins p × Tb R p) (fun z =>
        D x (simulate p z.1) ((mixT r a z.2).1, progRO p Hb (stOf x) z.1 (mixT r a z.2).2))| ≤
      ZKPRow.εP R p q3 q5 qE r.2.2.1.card r.2.2.2.card + r.1.card / 2 ^ 128 +
        h23G R p p.qsDegree r.2.2.1.card r.2.2.2.card r.2.1.card := by
  have hz := hzk x
  have hDx := hD x
  have hpx := hst x
  generalize stOf x = st at hz hpx ⊢
  subst hpx
  have h := zk_patched Hb st (wOf x) hlr hz hHb hsp (fun o g s => D x o (g, s)) hDx r.1 a.1 r.2.1
    a.2.1 r.2.2.1 a.2.2.1 r.2.2.2 a.2.2.2
  rw [← pr_equiv (Equiv.prodAssoc (Bytes 16) Tab3 (ShG R st.params)),
    ← pr_equiv (Equiv.prodAssoc (SimCoins st.params) Tab3 (ShG R st.params))]
  exact h

/-- **Zero knowledge for a statement chosen by an adversary that reads the tables**
(single proof, ROM and ideal cipher). The statement and witness are `stOf (S t)`, `wOf (S t)`
for an adversary `S` that reads the tables `t` (the proof's `H₃` slice and the shared `H₂³`, `H₅`
and cipher tables) at `s₃`, `s₂`, `s₅`, `s_E` keys (`SReads`); then the real prover runs on `t`
with a fresh `ρ`, or the simulator outputs a proof from its coins and programs `H₂³`. A
distinguisher sees `S`'s output, the proof and the (programmed) tables, reading the slice, `H₅` and
the cipher at `q₃`, `q₅`, `q_E` keys and `H₂³` freely. Its advantage is at most
`εAd d q₃ q₅ q_E s₃ s₂ s₅ s_E`. -/
theorem zk_adaptive [ZKPRow R] {X : Type*} (p : Params) (hlr : p.labelRows = true) (hsp : SmallParams p)
    (hHb : HashesWF Hb) (stOf : X → Statement) (wOf : X → ByteArray)
    (cs : X → ByteArray → ByteArray → System GF128) (hst : ∀ x, (stOf x).params = p)
    (hzk : ∀ x, ZKHyp CrtGen.tables (stOf x) (wOf x) (cs x)) (S : Tb R p → X)
    {s3 s2 s5 sE : ℕ} (hS : SReads p S s3 s2 s5 sE) {q3 q5 qE : ℕ}
    (D : X → Except String ByteArray → Tb R p → Prop)
    (hD : ∀ x, Budget p q3 q5 qE (fun o g s => D x o (g, s))) :
    |pr (Bytes 16 × Tb R p) (fun z =>
        D (S z.2) (realRO p Hb (stOf (S z.2)) (wOf (S z.2)) z.1 z.2.1 z.2.2) z.2) -
      pr (SimCoins p × Tb R p) (fun z =>
        D (S z.2) (simulate p z.1) (z.2.1, progRO p Hb (stOf (S z.2)) z.1 z.2.2))| ≤
      εAdG R p p.qsDegree q3 q5 qE s3 s2 s5 sE := by
  obtain ⟨Q, hQ, hc⟩ := hS
  have eR := pr_resample (C := Bytes 16) mixT AgT agT_mixT mixT_mixT S Q hQ
    (fun ρ x t => D x (realRO p Hb (stOf x) (wOf x) ρ t.1 t.2) t)
  have eS := pr_resample (C := SimCoins p) mixT AgT agT_mixT mixT_mixT S Q hQ
    (fun c x t => D x (simulate p c) (t.1, progRO p Hb (stOf x) c t.2))
  beta_reduce at eR eS
  rw [eR, eS]
  let eC : {C : Type} → [Fintype C] → Tb R p × (C × Tb R p) ≃ (C × Tb R p) × Tb R p := fun {C} _ =>
    { toFun := fun z => ((z.2.1, z.1), z.2.2)
      invFun := fun z => (z.1.2, (z.1.1, z.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv (eC (C := Bytes 16)), ← pr_equiv (eC (C := SimCoins p))]
  refine abs_pr_prod_sub_le _ _ fun a => ?_
  obtain ⟨c3, c2, c5, cE⟩ := hc a
  refine (zk_adaptive_inner Hb p hlr hsp hHb stOf wOf cs hst hzk D hD (S a) (Q a) a).trans ?_
  unfold εAdG
  have := ZKPRow.εP_mono (R := R) p (le_refl q3) (le_refl q5) (le_refl qE) c5 cE
  have := h23G_mono (R := R) p (d := p.qsDegree) c5 cE c2
  have : ((Q a).1.card : ℝ) ≤ s3 := by exact_mod_cast c3
  gcongr

/-- **The per-outer-table bound for a fixed statement and witness** (`zk_patched` on `mixT r a`). -/
theorem zk_adaptive_at [ZKPRow R] (p : Params) (hlr : p.labelRows = true) (hsp : SmallParams p)
    (hHb : HashesWF Hb) (st : Statement) (w : ByteArray) {cs : ByteArray → ByteArray → System GF128}
    (hpx : st.params = p) (hz : ZKHyp CrtGen.tables st w cs) {q3 q5 qE : ℕ}
    (D : Except String ByteArray → Tb R p → Prop) (hD : Budget p q3 q5 qE (fun o g s => D o (g, s)))
    (r : RS p) (a : Tb R p) :
    |pr (Bytes 16 × Tb R p) (fun z =>
        D (realRO p Hb st w z.1 (mixT r a z.2).1 (mixT r a z.2).2) (mixT r a z.2)) -
      pr (SimCoins p × Tb R p) (fun z =>
        D (simulate p z.1) ((mixT r a z.2).1, progRO p Hb st z.1 (mixT r a z.2).2))| ≤
      ZKPRow.εP R p q3 q5 qE r.2.2.1.card r.2.2.2.card + r.1.card / 2 ^ 128 +
        h23G R p p.qsDegree r.2.2.1.card r.2.2.2.card r.2.1.card := by
  subst hpx
  have h := zk_patched Hb st w hlr hz hHb hsp (fun o g s => D o (g, s)) hD r.1 a.1 r.2.1
    a.2.1 r.2.2.1 a.2.2.1 r.2.2.2 a.2.2.2
  rw [← pr_equiv (Equiv.prodAssoc (Bytes 16) Tab3 (ShG R st.params)),
    ← pr_equiv (Equiv.prodAssoc (SimCoins st.params) Tab3 (ShG R st.params))]
  exact h

/-- **The Lean prover is `ZeroKnowledgeROA`** (`Privacy/AdaptiveRO.lean`): for every relation whose
statements have dedicated label rows and parameters `p` and whose witnesses satisfy the
deterministic hypotheses, against table readers with budgets `(s₃, s₂, s₅, s_E)` (`SReads`) and
distinguishers with budgets `(q₃, q₅, q_E)` (`Budget`), with error `εAd`, the outputs mapped by any
`φ`. -/
theorem lean_zeroKnowledgeROA [ZKPRow R] {I W O : Type*} (p : Params) (stOf : I → Statement)
    (hp : ∀ x, (stOf x).params = p) (hlr : p.labelRows = true) (enc : I → W → ByteArray)
    (Rl : I → W → Prop) (cs : I → ByteArray → ByteArray → System GF128)
    (h : ∀ x w, Rl x w → ZKHyp CrtGen.tables (stOf x) (enc x w) (cs x)) (hHb : HashesWF Hb)
    (hsp : SmallParams p) (q3 q5 qE s3 s2 s5 sE : ℕ) (φ : Except String ByteArray → O) :
    ZeroKnowledgeROA Rl (fun x w ρ g (s : ShG R p) => φ (realRO p Hb (stOf x) (enc x w) ρ g s))
      (fun _ c => φ (simulate p c)) (fun x c (s : ShG R p) => progRO p Hb (stOf x) c s)
      (fun _ Sx => SReads p Sx s3 s2 s5 sE) (Budget p q3 q5 qE)
      (εAdG R p p.qsDegree q3 q5 qE s3 s2 s5 sE) := by
  intro _ Sx stw hS hR dummy D hD
  obtain ⟨Q, hQ, hc⟩ := hS
  refine abs_pr_resample_le (C := Bytes 16) (C' := SimCoins p) mixT AgT agT_mixT mixT_mixT Sx Q hQ
    (fun ρ x t => D x (outReal stw (fun x w ρ g s => φ (realRO p Hb (stOf x) (enc x w) ρ g s))
      dummy x ρ t.1 t.2) t.1 t.2)
    (fun c x t => D x (outSim stw (fun _ c => φ (simulate p c)) dummy x c) t.1
      (progSim stw (fun x c s => progRO p Hb (stOf x) c s) x c t.2)) fun a => ?_
  obtain ⟨c3, c2, c5, cE⟩ := hc a
  have hbound : ZKPRow.εP R p q3 q5 qE (Q a).2.2.1.card (Q a).2.2.2.card + (Q a).1.card / 2 ^ 128 +
      h23G R p p.qsDegree (Q a).2.2.1.card (Q a).2.2.2.card (Q a).2.1.card ≤
      εAdG R p p.qsDegree q3 q5 qE s3 s2 s5 sE := by
    unfold εAdG
    have := ZKPRow.εP_mono (R := R) p (le_refl q3) (le_refl q5) (le_refl qE) c5 cE
    have := h23G_mono (R := R) p (d := p.qsDegree) c5 cE c2
    have : ((Q a).1.card : ℝ) ≤ s3 := by exact_mod_cast c3
    gcongr
  rcases hx : stw (Sx a) with _ | ⟨i, w⟩
  · -- No statement: no proof, nothing programmed; the two sides are equal.
    simp only [outReal, outSim, progSim, hx, Option.elim]
    rw [pr_prod_snd (α := Bytes 16) (fun t : Tb R p => D (Sx a) dummy (mixT (Q a) a t).1
        (mixT (Q a) a t).2),
      pr_prod_snd (α := SimCoins p) (fun t : Tb R p => D (Sx a) dummy (mixT (Q a) a t).1
        (mixT (Q a) a t).2), sub_self, abs_zero]
    exact εAdG_nonneg _ _ _ _ _ _ _ _ _
  · have hz := h i w (hR _ i w hx)
    refine le_trans ?_ hbound
    simp only [outReal, outSim, progSim, hx, Option.elim]
    exact zk_adaptive_at Hb p hlr hsp hHb (stOf i) (enc i w) (hp i) hz
      (fun o t => D (Sx a) (φ o) t.1 t.2) (Budget.comp φ (hD (Sx a))) (Q a) a

/-- **The programming-collision bound for a proof whose statement is read off the tables**: a
programming `L x` at prefix blocks whose tails lie in a fixed set `T` changes the real proof
(of the statement `stw (S t)` chosen by a table reader `S` with budgets `(s₃, s₂, s₅, s_E)`) with
probability at most

    s₃·2⁻¹²⁸ + 2⁻¹¹⁰ + εROP(0, 312, 4607, s₅, s_E) + noHitProb + |T|·2^(−8·16(d−1)). -/
theorem pr_collide_adaptive [ZKPRow R] {X : Type*} (p : Params) (hlr : p.labelRows = true)
    (hsp : SmallParams p) (hHb : HashesWF Hb) (stw : X → Option (Statement × ByteArray))
    (cs : X → ByteArray → ByteArray → System GF128)
    (hst : ∀ x st w, stw x = some (st, w) → st.params = p ∧ ZKHyp CrtGen.tables st w (cs x))
    (S : Tb R p → X) {s3 s2 s5 sE : ℕ} (hS : SReads p S s3 s2 s5 sE) (L : X → ShG R p → ShG R p)
    (B : X → ShG R p → Finset (Bytes (preLen p))) (hL : ∀ x, ProgAt (L x) (B x))
    (T : Finset ByteArray) (hT : ∀ x s, ∀ b ∈ B x s, preTail b ∈ T) :
    pr (Bytes 16 × Tb R p) (fun z => (stw (S z.2)).elim False fun sw =>
        realRO p Hb sw.1 sw.2 z.1 z.2.1 (L (S z.2) z.2.2) ≠ realRO p Hb sw.1 sw.2 z.1 z.2.1 z.2.2) ≤
      s3 / 2 ^ 128 + (1 / 2 ^ 110 + ZKPRow.εP R p 0 312 4607 s5 sE +
        (noHitProb + T.card / 2 ^ (8 * (16 * (p.qsDegree - 1))))) := by
  classical
  obtain ⟨Q, hQ, hc⟩ := hS
  refine pr_resample_le (C := Bytes 16) mixT AgT agT_mixT mixT_mixT S Q hQ
    (fun ρ x t => (stw x).elim False fun sw =>
      realRO p Hb sw.1 sw.2 ρ t.1 (L x t.2) ≠ realRO p Hb sw.1 sw.2 ρ t.1 t.2) fun a => ?_
  obtain ⟨c3, c2, c5, cE⟩ := hc a
  have hnn : 0 ≤ s3 / 2 ^ 128 + (1 / 2 ^ 110 + ZKPRow.εP R p 0 312 4607 s5 sE +
      (noHitProb + T.card / 2 ^ (8 * (16 * (p.qsDegree - 1))))) := by
    have a1 := ZKPRow.εP_nonneg (R := R) p 0 312 4607 s5 sE
    have a2 : 0 ≤ noHitProb := pr_nonneg _
    have a3 : (0 : ℝ) ≤ s3 / 2 ^ 128 := div_nonneg (Nat.cast_nonneg _) (by norm_num)
    have a4 : (0 : ℝ) ≤ T.card / 2 ^ (8 * (16 * (p.qsDegree - 1))) :=
      div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)
    have a5 : (0 : ℝ) ≤ 1 / 2 ^ 110 := by norm_num
    linarith
  rcases hx : stw (S a) with _ | ⟨st, w⟩
  · simp only [Option.elim]
    rw [pr_false]
    exact hnn
  · obtain ⟨hpx, hz⟩ := hst _ st w hx
    subst hpx
    obtain ⟨hl1, -, -, hl2⟩ := labelRows_sizes hlr
    have hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows := by omega
    simp only [Option.elim]
    set r := Q a
    -- The event implies `ρ ∈ P3` or the real tail in `T`.
    have hsub : ∀ z : Bytes 16 × Tb R st.params,
        realRO st.params Hb st w z.1 (mixT r a z.2).1 (L (S a) (mixT r a z.2).2) ≠
          realRO st.params Hb st w z.1 (mixT r a z.2).1 (mixT r a z.2).2 →
        z.1 ∈ r.1 ∨ preTail (blk (preLen st.params) (preRO Hb st w z.1 z.2.1
          (patch5E r.2.2.1 a.2.2.1 r.2.2.2 a.2.2.2 z.2.2))) ∈ T := by
      intro z hne
      by_cases hρ : z.1 ∈ r.1
      · exact Or.inl hρ
      · right
        have hg : (mixT r a z.2).1 z.1 = z.2.1 z.1 := patchT_of_not_mem _ _ hρ
        rw [realRO_g3_congr hz hHb hlab z.1 _ hg, realRO_g3_congr hz hHb hlab z.1 _ hg] at hne
        by_contra hn
        refine hne (realRO_progAt hz hHb hlab (hL (S a)) z.1 z.2.1 _ fun hb => hn ?_)
        exact hT _ _ _ hb
    refine (pr_mono hsub).trans ((pr_or_le _ _).trans ?_)
    have hρ : pr (Bytes 16 × Tb R st.params) (fun z => z.1 ∈ r.1) ≤ s3 / 2 ^ 128 := by
      rw [pr_prod_fst (β := Tb R st.params) (fun ρ : Bytes 16 => ρ ∈ r.1)]
      have h1 : pr (Bytes 16) (fun ρ => ρ ∈ r.1) ≤ (r.1.card : ℝ) / 2 ^ 128 := by
        have := pr_mem_le (α := Bytes 16) id Function.injective_id r.1
        rw [card_bytes16] at this
        exact this.trans (le_of_eq (by norm_num))
      have : (r.1.card : ℝ) ≤ s3 := by exact_mod_cast c3
      exact h1.trans (by gcongr)
    have ht := pr_preTail_mem hlr hz hHb hsp r.2.2.1 a.2.2.1 r.2.2.2 a.2.2.2 T
    have hm := ZKPRow.εP_mono (R := R) st.params (le_refl 0) (le_refl 312) (le_refl 4607) c5 cE
    have ht' : pr (Bytes 16 × Tb R st.params) (fun z => preTail (blk (preLen st.params)
        (preRO Hb st w z.1 z.2.1 (patch5E r.2.2.1 a.2.2.1 r.2.2.2 a.2.2.2 z.2.2))) ∈ T) ≤
        1 / 2 ^ 110 + ZKPRow.εP R st.params 0 312 4607 s5 sE +
          (noHitProb + T.card / 2 ^ (8 * (16 * (st.params.qsDegree - 1)))) := by
      rw [← pr_equiv (Equiv.prodAssoc (Bytes 16) Tab3 (ShG R st.params))]
      refine ht.trans ?_
      linarith
    linarith

end Adaptive

/-! ## Consistent table readers -/

section SReadsCalc

variable {R : Type} {p : Params}

/-- The union of two read sets. -/
def RS.union (r r' : RS p) : RS p := (r.1 ∪ r'.1, r.2.1 ∪ r'.2.1, r.2.2.1 ∪ r'.2.2.1, r.2.2.2 ∪ r'.2.2.2)

lemma AgT.left {r r' : RS p} {t t' : Tb R p} (h : AgT (r.union r') t t') : AgT r t t' :=
  ⟨fun k hk => h.1 k (Finset.mem_union_left _ hk), fun k hk => h.2.1 k (Finset.mem_union_left _ hk),
    fun k hk => h.2.2.1 k (Finset.mem_union_left _ hk),
    fun k hk => h.2.2.2 k (Finset.mem_union_left _ hk)⟩

lemma AgT.right {r r' : RS p} {t t' : Tb R p} (h : AgT (r.union r') t t') : AgT r' t t' :=
  ⟨fun k hk => h.1 k (Finset.mem_union_right _ hk),
    fun k hk => h.2.1 k (Finset.mem_union_right _ hk),
    fun k hk => h.2.2.1 k (Finset.mem_union_right _ hk),
    fun k hk => h.2.2.2 k (Finset.mem_union_right _ hk)⟩

variable {X Y : Type*}

lemma SReads.const (x : X) : SReads p (fun _ : Tb R p => x) 0 0 0 0 :=
  ⟨fun _ => (∅, ∅, ∅, ∅), fun _ _ _ => ⟨rfl, rfl⟩, fun _ => by simp⟩

lemma SReads.mono {f : Tb R p → X} {a3 a2 a5 aE b3 b2 b5 bE : ℕ} (h : SReads p f a3 a2 a5 aE)
    (h3 : a3 ≤ b3) (h2 : a2 ≤ b2) (h5 : a5 ≤ b5) (hE : aE ≤ bE) : SReads p f b3 b2 b5 bE := by
  obtain ⟨Q, hQ, hc⟩ := h
  exact ⟨Q, hQ, fun t => ⟨(hc t).1.trans h3, (hc t).2.1.trans h2, (hc t).2.2.1.trans h5,
    (hc t).2.2.2.trans hE⟩⟩

/-- **Sequencing**: `g` run on `f`'s output reads what `f` reads and what `g` reads. -/
lemma SReads.bind {f : Tb R p → Y} {g : Y → Tb R p → X} {a3 a2 a5 aE b3 b2 b5 bE : ℕ}
    (hf : SReads p f a3 a2 a5 aE) (hg : ∀ y, SReads p (g y) b3 b2 b5 bE) :
    SReads p (fun t => g (f t) t) (a3 + b3) (a2 + b2) (a5 + b5) (aE + bE) := by
  classical
  obtain ⟨Qf, hQf, hcf⟩ := hf
  choose Qg hQg hcg using hg
  refine ⟨fun t => (Qf t).union (Qg (f t) t), fun t t' h => ?_, fun t => ?_⟩
  · obtain ⟨e1, e2⟩ := hQf t t' h.left
    obtain ⟨e3, e4⟩ := hQg (f t) t t' h.right
    refine ⟨?_, ?_⟩
    · show (Qf t').union (Qg (f t') t') = (Qf t).union (Qg (f t) t)
      rw [e1, e2, e3]
    · show g (f t') t' = g (f t) t
      rw [e2, e4]
  · obtain ⟨a1, a2', a3', a4⟩ := hcf t
    obtain ⟨b1, b2', b3', b4⟩ := hcg (f t) t
    exact ⟨(card_union_le _ _).trans (add_le_add a1 b1), (card_union_le _ _).trans (add_le_add a2' b2'),
      (card_union_le _ _).trans (add_le_add a3' b3'), (card_union_le _ _).trans (add_le_add a4 b4)⟩

lemma SReads.map {f : Tb R p → Y} {a3 a2 a5 aE : ℕ} (hf : SReads p f a3 a2 a5 aE) (φ : Y → X) :
    SReads p (fun t => φ (f t)) a3 a2 a5 aE := by
  simpa using hf.bind (g := fun y _ => φ y) fun y => SReads.const (φ y)

lemma SReads.pair {f : Tb R p → Y} {g : Tb R p → X} {a3 a2 a5 aE b3 b2 b5 bE : ℕ}
    (hf : SReads p f a3 a2 a5 aE) (hg : SReads p g b3 b2 b5 bE) :
    SReads p (fun t => (f t, g t)) (a3 + b3) (a2 + b2) (a5 + b5) (aE + bE) :=
  hf.bind (g := fun y t => (y, g t)) fun y => hg.map fun x => (y, x)

/-- **A table reader with the shared tables fixed** reads its slice at at most `a₃` keys; with the
slice fixed it reads `H₅` and the cipher at at most `a₅`, `a_E` keys. -/
lemma SReads.rd3 {f : Tb R p → X} {a3 a2 a5 aE : ℕ} (h : SReads p f a3 a2 a5 aE) (s : ShG R p) :
    Rd3 (fun g => f (g, s)) a3 := by
  obtain ⟨Q, hQ, hc⟩ := h
  exact ⟨fun g => (Q (g, s)).1, fun g => (hc _).1, fun g g' hg =>
    (hQ (g, s) (g', s) ⟨hg, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩).2⟩

lemma SReads.rd5 {f : Tb R p → X} {a3 a2 a5 aE : ℕ} (h : SReads p f a3 a2 a5 aE) (g : Tab3) :
    Rd5 (fun s => f (g, s)) a5 := by
  obtain ⟨Q, hQ, hc⟩ := h
  exact ⟨fun s => (Q (g, s)).2.2.1, fun s => (hc _).2.2.1, fun s G5 h5 =>
    (hQ (g, s) (g, (s.1, G5, s.2.2)) ⟨fun _ _ => rfl, fun _ _ => rfl, h5, fun _ _ => rfl⟩).2⟩

lemma SReads.rdE {f : Tb R p → X} {a3 a2 a5 aE : ℕ} (h : SReads p f a3 a2 a5 aE) (g : Tab3) :
    RdE (fun s => f (g, s)) aE := by
  obtain ⟨Q, hQ, hc⟩ := h
  exact ⟨fun s => (Q (g, s)).2.2.2, fun s => (hc _).2.2.2, fun s E hE =>
    (hQ (g, s) (g, (s.1, s.2.1, E)) ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, hE⟩).2⟩

/-- **A consistent programming of `H₂³`**: `L` changes only `H₂³`, there only at keys of the
blocks `Bk s`, and its blocks, its programmed answers and its reads `R5 s`, `RE s` of `H₅` and the
cipher are determined by the tables on those reads (at most `m₅`, `m_E` keys). -/
def CProg (L : ShG R p → ShG R p) (m5 mE : ℕ) : Prop :=
  ∃ (Bk : ShG R p → Finset (Bytes (preLen p))) (R5 : ShG R p → Finset (Bytes 37))
    (RE : ShG R p → Finset Blk),
    (∀ s, (L s).2 = s.2) ∧ (∀ s (k : K2 p), k.1 ∉ Bk s → (L s).1 k = s.1 k) ∧
    (∀ s s', (∀ k ∈ R5 s, s.2.1 k = s'.2.1 k) → (∀ k ∈ RE s, s.2.2 k = s'.2.2 k) →
      R5 s' = R5 s ∧ RE s' = RE s ∧ Bk s' = Bk s ∧ ∀ k : K2 p, k.1 ∈ Bk s → (L s').1 k = (L s).1 k) ∧
    ∀ s, (R5 s).card ≤ m5 ∧ (RE s).card ≤ mE

/-- **Reading through a consistent programming** reads what the reader reads and what the
programming reads. -/
lemma SReads.comp_prog {f : Tb R p → X} {a3 a2 a5 aE m5 mE : ℕ} (hf : SReads p f a3 a2 a5 aE)
    {L : ShG R p → ShG R p} (hL : CProg L m5 mE) :
    SReads p (fun t => f (t.1, L t.2)) a3 a2 (a5 + m5) (aE + mE) := by
  classical
  obtain ⟨Q, hQ, hc⟩ := hf
  obtain ⟨Bk, R5, RE, h2, hoff, hcons, hcard⟩ := hL
  let Q' : Tb R p → RS p := fun t => ((Q (t.1, L t.2)).1, (Q (t.1, L t.2)).2.1,
    (Q (t.1, L t.2)).2.2.1 ∪ R5 t.2, (Q (t.1, L t.2)).2.2.2 ∪ RE t.2)
  refine ⟨Q', fun t t' h => ?_, fun t => ?_⟩
  · obtain ⟨h3, h22, h5, hE⟩ := h
    obtain ⟨e5, eE, eB, ev⟩ := hcons t.2 t'.2 (fun k hk => h5 k (Finset.mem_union_right _ hk))
      (fun k hk => hE k (Finset.mem_union_right _ hk))
    have hag : AgT (Q (t.1, L t.2)) (t.1, L t.2) (t'.1, L t'.2) := by
      refine ⟨fun k hk => h3 k hk, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
      · show (L t.2).1 k = (L t'.2).1 k
        by_cases hb : k.1 ∈ Bk t.2
        · exact (ev k hb).symm
        · rw [hoff _ k hb, hoff _ k (by rw [eB]; exact hb)]
          exact h22 k hk
      · show (L t.2).2.1 k = (L t'.2).2.1 k
        rw [h2, h2]
        exact h5 k (Finset.mem_union_left _ hk)
      · show (L t.2).2.2 k = (L t'.2).2.2 k
        rw [h2, h2]
        exact hE k (Finset.mem_union_left _ hk)
    obtain ⟨e1, e2⟩ := hQ _ _ hag
    refine ⟨?_, e2⟩
    show ((Q (t'.1, L t'.2)).1, (Q (t'.1, L t'.2)).2.1, (Q (t'.1, L t'.2)).2.2.1 ∪ R5 t'.2,
        (Q (t'.1, L t'.2)).2.2.2 ∪ RE t'.2) = Q' t
    rw [e1, e5, eE]
  · obtain ⟨c1, c2, c3, c4⟩ := hc (t.1, L t.2)
    exact ⟨c1, c2, (card_union_le _ _).trans (add_le_add c3 (hcard t.2).1),
      (card_union_le _ _).trans (add_le_add c4 (hcard t.2).2)⟩

/-- The identity is a consistent programming. -/
lemma CProg.id : CProg (fun s : ShG R p => s) 0 0 :=
  ⟨fun _ => ∅, fun _ => ∅, fun _ => ∅, fun _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ _ => ⟨rfl, rfl, rfl, fun _ h => absurd h (Finset.notMem_empty _)⟩, fun _ => by simp⟩

/-- A programming applied under a condition that does not read the tables. -/
lemma CProg.ite {L : ShG R p → ShG R p} {m5 mE : ℕ} (c : Prop) [Decidable c] (h : CProg L m5 mE) :
    CProg (fun s => if c then L s else s) m5 mE := by
  by_cases hc : c
  · simpa only [hc, ↓reduceIte] using h
  · simp only [hc, ↓reduceIte]
    obtain ⟨Bk, R5, RE, h2, hoff, hcons, hcard⟩ := CProg.id (p := p)
    exact ⟨Bk, R5, RE, h2, hoff, hcons, fun s => ⟨(hcard s).1.trans (Nat.zero_le _),
      (hcard s).2.trans (Nat.zero_le _)⟩⟩

end SReadsCalc

/-! ## The simulator's programming is a consistent programming -/

section ProgCons

variable {R : Type} [CipherRow R] {p : Params} {Hb : Hashes} {st : Statement}

/-- The reconstruction's reads are consistent: a table that agrees on them reads the same keys. -/
theorem rdKeys_ic_congr {E E' : Cipher} {iv opening delta : ByteArray}
    (h : ∀ k ∈ rdKeys E iv opening delta, E k = E' k) :
    rdKeys E' iv opening delta = rdKeys E iv opening delta := by
  unfold rdKeys
  rw [recTree_ic_congr h]

/-- **The verifier's `H₅` inputs read the cipher only at the reconstruction's reads.** -/
theorem vIn5_ic_congr (Hs : Hashes) (T : CrtTables) (st : Statement) (proof : ByteArray)
    {E E' : Cipher}
    (h : ∀ k ∈ rdKeys E (ivOf Hs ⟨st.params, proof⟩ (st.mu1 Hs)) (⟨st.params, proof⟩ : Proof).opening
      (⟨st.params, proof⟩ : Proof).delta, E k = E' k) :
    @vIn5 (icPrg E) Hs T st proof = @vIn5 (icPrg E') Hs T st proof := by
  set pf : Proof := ⟨st.params, proof⟩ with hpf
  have hr := reconstruct_ic_congr h
  unfold vIn5
  rcases hl : @BAVC.reconstruct (icPrg E) (ivOf Hs pf (st.mu1 Hs)) pf.opening pf.delta with _ | leaves
  · simp only [← hpf, ← hr, hl]
  · have hc : @convertToVole (icPrg E) pf (ivOf Hs pf (st.mu1 Hs)) leaves =
        @convertToVole (icPrg E') pf (ivOf Hs pf (st.mu1 Hs)) leaves := by
      unfold convertToVole
      refine convertToVoleAt_ic_congr _ _ _ _ _ fun i hi j hj hjd hs => h _ ?_
      have := @leafKey_mem_rdKeys E (ivOf Hs pf (st.mu1 Hs)) pf.opening pf.delta i j hi hj hjd
      rw [hl, Option.getD_some] at this
      exact this hs
    simp only [← hpf, ← hr, hl, hc]

lemma ivOf_rec5 (G5 : Tab5F) (pf : Proof) :
    ivOf (rec5 Hb G5) pf (st.mu1 (rec5 Hb G5)) = ivOf Hb pf (st.mu1 Hb) := by
  unfold ivOf
  rw [rec5_h4, rec5_mu1]

/-- The simulator's programmed answers at its block. -/
lemma progRO_fst_blk (c : SimCoins p) (s : ShG R p) (k2 : Fin nGrind) :
    (progRO p Hb st c s).1 (simBlk Hb st c s, k2) = c.1.2.1 k2 :=
  programAt_apply_pt (x := key2 p (@outPre (icPrg (rowFn s.2.2)) Hb CrtGen.tables st s.2.1 (simulate p c)))
    (key2_injective _ _) c.1.2.1 s.1 k2

/-- **The simulator's programming is a consistent programming** of one block, reading `H₅` at
`312` and the cipher at `4607` keys. -/
theorem progRO_cprog (c : SimCoins p) : CProg (progRO (R := R) p Hb st c) 312 4607 := by
  classical
  refine ⟨fun s => {simBlk Hb st c s}, progKeys5 Hb st (simulate p c),
    progKeysE Hb st (simulate p c), fun _ => rfl, fun s k hk => ?_, fun s s' h5 hE => ?_,
    fun s => ⟨?_, ?_⟩⟩
  · refine programAt_apply_of_ne _ _ fun i hi => hk ?_
    rw [← hi, Finset.mem_singleton]
    rfl
  · -- The recomputed prefix and the reads agree.
    have hpre : ∀ o : Except String ByteArray,
        (∀ k ∈ progKeys5 Hb st o s, s.2.1 k = s'.2.1 k) →
        (∀ k ∈ progKeysE Hb st o s, s.2.2 k = s'.2.2 k) →
        @outPre (icPrg (rowFn s'.2.2)) Hb CrtGen.tables st s'.2.1 o =
          @outPre (icPrg (rowFn s.2.2)) Hb CrtGen.tables st s.2.1 o ∧
        progKeys5 Hb st o s' = progKeys5 Hb st o s ∧ progKeysE Hb st o s' = progKeysE Hb st o s := by
      intro o h5 hE
      cases o with
      | error e => exact ⟨rfl, rfl, rfl⟩
      | ok b =>
        simp only [progKeys5, progKeysE] at h5 hE
        replace hE := fun k hk => rowFn_congr (hE k hk)
        simp only [progKeys5, progKeysE, outPre]
        have hiv : ∀ G5 : Tab5F, ivOf (rec5 Hb G5) ⟨st.params, b⟩ (st.mu1 (rec5 Hb G5)) =
            ivOf Hb ⟨st.params, b⟩ (st.mu1 Hb) := fun G5 => ivOf_rec5 G5 _
        have hmu : st.mu1 (rec5 Hb s'.2.1) = st.mu1 (rec5 Hb s.2.1) := by rw [rec5_mu1, rec5_mu1]
        have h4 : (rec5 Hb s'.2.1).hash .h4 = (rec5 Hb s.2.1).hash .h4 := by rw [rec5_h4, rec5_h4]
        have hv5 : @vIn5 (icPrg (rowFn s'.2.2)) (rec5 Hb s'.2.1) CrtGen.tables st b =
            @vIn5 (icPrg (rowFn s.2.2)) (rec5 Hb s.2.1) CrtGen.tables st b := by
          rw [@vIn5_congr (icPrg (rowFn s'.2.2)) _ st _ _ hmu h4]
          exact (vIn5_ic_congr _ _ _ _ hE).symm
        refine ⟨?_, by rw [hv5], ?_⟩
        · have hA : (rec5 Hb s'.2.1).AgreeOff .h5 (rec5 Hb s.2.1) := by
            intro k hk; rw [rec5_agree_ne hk, rec5_agree_ne hk]
          have e1 : @vPre (icPrg (rowFn s'.2.2)) (rec5 Hb s'.2.1) CrtGen.tables st b =
              @vPre (icPrg (rowFn s'.2.2)) (rec5 Hb s.2.1) CrtGen.tables st b := by
            refine @vPre_h5_congr (icPrg (rowFn s'.2.2)) _ _ hA _ _ _ fun x hx => ?_
            rw [hv5] at hx
            refine withTable_h5_congr _ fun _ => ?_
            exact (h5 _ (mem_image.2 ⟨x, List.mem_toFinset.2 hx, rfl⟩)).symm
          rw [e1]
          exact (vPre_ic_congr _ _ _ _ hE).symm
        · rw [hiv s'.2.1]
          rw [hiv s.2.1] at hE ⊢
          exact rdKeys_ic_congr hE
    obtain ⟨e1, e2, e3⟩ := hpre (simulate p c) h5 hE
    have hblk : simBlk Hb st c s' = simBlk Hb st c s := by
      unfold simBlk; rw [e1]
    refine ⟨e2, e3, congrArg (fun x => ({x} : Finset _)) hblk, fun k hk => ?_⟩
    obtain ⟨k1, k2⟩ := k
    rw [Finset.mem_singleton] at hk
    dsimp only at hk
    subst hk
    calc (progRO p Hb st c s').1 (simBlk Hb st c s, k2)
        = (progRO p Hb st c s').1 (simBlk Hb st c s', k2) := by rw [hblk]
      _ = c.1.2.1 k2 := progRO_fst_blk c s' k2
      _ = (progRO p Hb st c s).1 (simBlk Hb st c s, k2) := (progRO_fst_blk c s k2).symm
  · unfold progKeys5
    split
    · exact card_image_le.trans ((List.toFinset_card_le _).trans
        (@vIn5_length_le (icPrg (rowFn s.2.2)) _ _ _ _))
    · simp
  · unfold progKeysE
    split
    · exact rdKeys_card _ _ _ _
    · simp

end ProgCons

end VoleMole.ZK.Sim
