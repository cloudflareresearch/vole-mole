import VoleMole.ZK.HopsMain

/-!
# The executable prover in the joint hop on `main` (`Privacy/MainChain.lean`)

`Privacy/MainChain.lean` composes four proofs in sequence abstractly. Here the slots are the
executable prover in the model of `zk_rom_ic` (each proof with its own uniform tables `H₃`, `H₂³`,
`H₅` and BAVC cipher; the adversary sees `H₃`, `H₅` and the cipher of every proof, `Vis p`), with
`main`'s layout (`MainP`):

* `realSlot`: the prover `proveE` with the executable grinding prefix (`proveE_recOf_aes`: at AES
  it is `Prover.prove`); `simSlot`: the simulator `simulate`;
* `mainH`: the ideal-tape prover with explicit sibling answers, as an `HSlot` (its `H₅` reads are
  `proverKeys`, its sibling keys `sibKey`);
* `real_fill_close`: real against `(mainH).fillS` is H1, grinding, H4 and the tape steps of
  `zk_rom_ic` (`joint_h1` … `joint_tape`), `q₃·2⁻¹²⁸ + 221·(4607 + q_E)·2⁻¹²⁸` against a
  distinguisher that reads `H₃` at `q₃` and the cipher at `q_E` keys;
* `ideal_sim_close`: `(mainH).idealS` against the simulator is exact (`joint_sim`);
* `idealP`, `simP`, `ideal_sim_closeP`, `bad_predJ`: the bad event of `mainH` (a sibling key among
  the prover's keys or a read set) implies that the witness prefix `w[0..16)` lies in the
  candidate set (`candidates`) of the read set, computed from the shared tape, the corrections and
  `d`; and these, with the output, are distributed in the ideal slot as in the simulator. So the
  bad event becomes a prediction of `w[0..16)` from the **simulated** proofs.
* **`main_chain_le`**: for any game of four `main`-layout proofs (`Game`) and any adversary `F`
  that reads `H₃` and the cipher of each proof at `q₃`, `q_E` keys and `H₅` with consistent read
  sets (`VCons`),

      |Pr[real] − Pr[sim]| ≤ 4·(q₃·2⁻¹²⁸ + 221·(4607 + q_E)·2⁻¹²⁸) + 15·Pr_sim[predAll]

  where `predAll` is the event that some proof's witness prefix is among the candidates of its
  `H₅` read set, in the game with all four proofs simulated.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy
open VoleMole.Privacy.MainChain

attribute [local instance] decEqW128

-- The provers and the simulator are reasoned about through lemmas only: unfolding them while
-- unifying (to evaluate the grinding search over `2³²` counters) is never useful.
attribute [local irreducible] simulate proveIdeal proveE firstHit

variable [HasPrg]

/-- A statement with its parameters set to `p` (so that its tables have the slot's types). -/
abbrev withP (st : Statement) (p : Params) : Statement := { st with params := p }

@[simp] lemma withP_params (st : Statement) (p : Params) : (withP st p).params = p := rfl

/-- A statement and a witness. -/
abbrev SW := Statement × ByteArray

/-- A proof, or the prover's error. -/
abbrev Out := Except String ByteArray

/-! ## The prover's `H₅` reads -/

section Keys

variable {Hs Hs' : Hashes} {k : Kind} (hu : Unread k) (h : Hs.AgreeOff k Hs') (T : CrtTables)
  (st : Statement)
include hu h

lemma actInputs_agreeOff : actInputs Hs T st = actInputs Hs' T st := by
  funext s t
  unfold actInputs qcolsTape
  rw [h.pubOf' hu st]

lemma proverKeys_agreeOff (x : IdealTape st.params) :
    proverKeys Hs T st x = proverKeys Hs' T st x := by
  ext k
  rw [mem_proverKeys, mem_proverKeys, sEnc_agreeOff hu h, actInputs_agreeOff hu h]

lemma sibKey_agreeOff : sibKey Hs T st = sibKey Hs' T st := by
  funext c e
  unfold sibKey
  rw [sEnc_agreeOff hu h]

end Keys

lemma proverKeys_withSib (Hs : Hashes) (T : CrtTables) (st : Statement) (s : Shared)
    (u : PadsU st.params) (z z' : Sib) :
    proverKeys Hs T st (s, withSib u z) = proverKeys Hs T st (s, withSib u z') := by
  ext k
  rw [mem_proverKeys, mem_proverKeys]
  rfl

/-! ## The slots -/

section Slots

variable (Hb : Hashes) (T : CrtTables) (p : Params)

/-- **The real prover** (`proveE` with the executable grinding prefix), its tables observed. -/
noncomputable def realSlot : Slot SW Out (Vis p) where
  K := (Bytes 16 × Tab2) × Vis p
  run y c := proveE (recOf Hb T (withP y.1 p) y.2 (preReal Hb (withP y.1 p) y.2 T c.2.2.1 c.2.2.2)
    c.2.1 c.1.2 c.2.2.1) T (withP y.1 p) y.2 c.2.2.2
    (preReal Hb (withP y.1 p) y.2 T c.2.2.1 c.2.2.2) c.1.1
  obs _ c := c.2

/-- **The simulator**, the tables independent. -/
noncomputable def simSlot : Slot SW Out (Vis p) where
  K := SimCoins p × Vis p
  run _ c := simulate p c.1
  obs _ c := c.2

/-- The base record of the `H₅` table in `recP` (the `H₃` and `H₂³` tables on top of `Hb`). -/
noncomputable abbrev baseP (st : Statement) (w : ByteArray) (G3 : Tab3) : Hashes :=
  (Hb.withTable .h3 (seedInput (st.mu1 Hb) (w.extract 0 st.params.witnessBytes)) G3).withTable .h23
    (gEnc fun _ => ByteArray.empty) fun _ => 0

lemma baseP_agreeOff (st : Statement) (w : ByteArray) (G3 : Tab3) :
    ∀ x : IdealTape st.params, proverKeys (baseP Hb st w G3) T st x = proverKeys Hb T st x := by
  intro x
  have a1 : (baseP Hb st w G3).AgreeOff .h23 (Hb.withTable .h3 (seedInput (st.mu1 Hb)
      (w.extract 0 st.params.witnessBytes)) G3) :=
    ((Hb.withTable .h3 _ G3).agreeOff_withTable .h23 _ _).symm
  have a2 : (Hb.withTable .h3 (seedInput (st.mu1 Hb)
      (w.extract 0 st.params.witnessBytes)) G3).AgreeOff .h3 Hb :=
    (Hb.agreeOff_withTable .h3 _ G3).symm
  rw [proverKeys_agreeOff unread_h23 a1, proverKeys_agreeOff unread_h3 a2]

lemma baseP_sibKey (st : Statement) (w : ByteArray) (G3 : Tab3) :
    sibKey (baseP Hb st w G3) T st = sibKey Hb T st := by
  have a1 : (baseP Hb st w G3).AgreeOff .h23 (Hb.withTable .h3 (seedInput (st.mu1 Hb)
      (w.extract 0 st.params.witnessBytes)) G3) :=
    ((Hb.withTable .h3 _ G3).agreeOff_withTable .h23 _ _).symm
  have a2 : (Hb.withTable .h3 (seedInput (st.mu1 Hb)
      (w.extract 0 st.params.witnessBytes)) G3).AgreeOff .h3 Hb :=
    (Hb.agreeOff_withTable .h3 _ G3).symm
  rw [sibKey_agreeOff unread_h23 a1, sibKey_agreeOff unread_h3 a2]

/-- **The sibling answers of `recP` are its `H₅` table at the sibling keys.** -/
lemma fillSib_recP (st : Statement) (w : ByteArray) (G3 : Tab3) (G5 : Tab5 st.params)
    (c : Shared × PadsU st.params) (z : Sib) :
    fillSib (recP Hb T st w G3 G5) T st (c.1, withSib c.2 z) =
      (c.1, withSib c.2 (G5 ∘ sibKey Hb T st c)) := by
  rw [recP_eq_H5, H5, fillSib_withTable, ← baseP_sibKey Hb T st w G3]

/-- The ideal-tape prover's output with explicit sibling answers `u`, `H₅` table `g` and the
other tables `v = (G3, E)`. -/
noncomputable def mainOut (y : SW) (c : Shared × PadsU p) (u : Fin 312 → Bytes 4)
    (g : SKey p → Bytes 4) (v : Tab3 × Cipher) : Out :=
  proveIdeal (recP Hb T (withP y.1 p) y.2 v.1 g) T (withP y.1 p) y.2 (c.1, withSib c.2 u)

/-- The prover's `H₅` keys. -/
noncomputable def mainPk (y : SW) (c : Shared × PadsU p) : Finset (SKey p) :=
  proverKeys Hb T (withP y.1 p) (c.1, withSib c.2 fun _ _ => 0)

lemma mainOut_congr (hm : MainP p) (y : SW) (c : Shared × PadsU p) (u : Fin 312 → Bytes 4)
    (g g' : SKey p → Bytes 4) (v : Tab3 × Cipher) (h : ∀ k ∈ mainPk Hb T p y c, g k = g' k) :
    mainOut Hb T p y c u g v = mainOut Hb T p y c u g' v := by
  unfold mainOut
  rw [recP_eq_H5, recP_eq_H5]
  refine proveIdeal_table_congr _ T (withP y.1 p) y.2 hm.hlab _ g g' fun k hk => h k ?_
  rw [← baseP, baseP_agreeOff Hb T, proverKeys_withSib] at hk
  exact hk

/-- **The ideal-tape prover with explicit sibling answers**, as an `HSlot` (`main`'s layout). -/
noncomputable def mainH (hm : MainP p) : HSlot SW Out where
  C := Shared × PadsU p
  ι := Fin 312
  Kt := SKey p
  V := Tab3 × Cipher
  R := Bytes 4
  out := mainOut Hb T p
  key y c := sibKey Hb T (withP y.1 p) c
  key_inj y c := sibKey_injective Hb T (withP y.1 p) c
  pk := mainPk Hb T p
  out_congr := mainOut_congr Hb T p hm

variable {p}

/-- The tables an `mainH` observation shows: `H₃`, `H₅`, the cipher. -/
def visOf (hm : MainP p) (ω : (mainH Hb T p hm).Obs) : Vis p := (ω.2.2.2.1, ω.2.2.1, ω.2.2.2.2)

/-- The coins of `mainH` as an ideal tape and the tables. -/
def coinsEquiv (hm : MainP p) : (mainH Hb T p hm).Coins ≃ IdealTape p × Vis p where
  toFun k := ((k.1.1, withSib k.1.2 k.2.1), (k.2.2.2.1, k.2.2.1, k.2.2.2.2))
  invFun c := ((c.1.1, dropSib c.1.2), c.1.2.2.2.2.2.2.2, c.2.2.1, (c.2.1, c.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The statement and witness are valid: some system for which the deterministic hypotheses hold. -/
def ValidZK (T : CrtTables) (p : Params) (y : SW) : Prop :=
  ∃ cs : ByteArray → ByteArray → System GF128, ZKHyp T (withP y.1 p) y.2 cs

/-- A reader of the tables that reads `H₃` at `q₃` keys and the cipher at `q_E` keys. -/
def RdV (q3 qE : ℕ) (f : Vis p → Prop) : Prop :=
  (∃ Q3 : Tab3 → Tab5 p → Cipher → Finset (Bytes 16), (∀ G3 G5 E, (Q3 G3 G5 E).card ≤ q3) ∧
    ∀ G3 G3' G5 E, (∀ k ∈ Q3 G3 G5 E, G3 k = G3' k) → (f (G3, G5, E) ↔ f (G3', G5, E))) ∧
  (∃ QE : Tab3 → Tab5 p → Cipher → Finset Blk, (∀ G3 G5 E, (QE G3 G5 E).card ≤ qE) ∧
    ∀ G3 G5 E E', (∀ k ∈ QE G3 G5 E, E k = E' k) → (f (G3, G5, E) ↔ f (G3, G5, E')))

/-- The pre-H6 hops' error. -/
noncomputable def εRF (q3 qE : ℕ) : ℝ := q3 / 2 ^ 128 + 221 * (4607 + qE) / 2 ^ 128

lemma εRF_nonneg (q3 qE : ℕ) : 0 ≤ εRF q3 qE := by
  unfold εRF
  apply add_nonneg <;> apply div_nonneg <;> positivity

lemma mainH_out (hm : MainP p) : (mainH Hb T p hm).out = mainOut Hb T p := rfl

lemma mainH_key (hm : MainP p) (y : SW) (c : Shared × PadsU p) :
    (mainH Hb T p hm).key y c = sibKey Hb T (withP y.1 p) c := rfl

/-- The filled slot's output, through `fillSib_recP`. -/
lemma mainOut_fill (st : Statement) (w : ByteArray) (c : Shared × PadsU p) (u : Fin 312 → Bytes 4)
    (g : SKey p → Bytes 4) (v : Tab3 × Cipher) :
    mainOut Hb T p (st, w) c (g ∘ sibKey Hb T (withP st p) c) g v =
      proveIdeal (recP Hb T (withP st p) w v.1 g) T (withP st p) w
        (fillSib (recP Hb T (withP st p) w v.1 g) T (withP st p) (c.1, withSib c.2 u)) := by
  rw [fillSib_recP Hb T (withP st p) w v.1 g c u]
  rfl

lemma pr_vis_coins (hm : MainP p) (D : Vis p → Prop) :
    pr (mainH Hb T p hm).Coins (fun k => D (visOf Hb T hm ((mainH Hb T p hm).obsOf none k))) =
      pr (Vis p) D := by
  rw [← pr_equiv (coinsEquiv Hb T hm).symm]
  exact pr_prod_snd (α := IdealTape p) D

/-- **Real to the ideal tape with the table's sibling answers** (H1, grinding, H4, tape). -/
theorem real_fill_close (hm : MainP p) (hp : SmallParams p) (q3 qE : ℕ) :
    Slot.Close (fun D : Option Out → Vis p → Prop => ∀ o, RdV q3 qE (D o)) (ValidZK T p)
      (εRF q3 qE) (realSlot Hb T p) ((mainH Hb T p hm).fillS.mapObs (visOf Hb T hm)) := by
  intro y hy D hD
  rcases y with _ | ⟨st, w⟩
  · have e1 : pr (realSlot Hb T p).K (fun k => D none k.2) = pr (Vis p) (D none) :=
      pr_prod_snd (α := Bytes 16 × Tab2) (D none)
    have e2 := pr_vis_coins Hb T hm (D none)
    refine le_of_eq_of_le ?_ (εRF_nonneg q3 qE)
    rw [abs_eq_zero, sub_eq_zero]
    exact e1.trans e2.symm
  obtain ⟨cs, hzk⟩ := hy (st, w) rfl
  let D' : Out → Vis p → Prop := fun o v => D (some o) v
  choose Q3 hq3 hQ3 using fun o => (hD (some o)).1
  choose QE hqE hQE using fun o => (hD (some o)).2
  have h1 := joint_h1 Hb T (withP st p) w (preReal Hb (withP st p) w T) D' Q3 (fun o G3 G3' G5 E h => hQ3 o G3 G3' G5 E h)
    (fun o => hq3 o)
  have h2 := joint_grind Hb T (withP st p) w (preReal Hb (withP st p) w T) D'
  have h3 := joint_h4 Hb T (withP st p) w hp D' QE (fun o G3 G5 E E' h => hQE o G3 G5 E E' h) (fun o => hqE o)
  have h4 := joint_tape Hb T (withP st p) w D'
  dsimp only [withP_params] at h1 h2 h3 h4
  have e : pr (IdealTape p × Vis p) (fun c => D' (proveIdeal (recP Hb T (withP st p) w c.2.1 c.2.2.1) T (withP st p) w
      (fillSib (recP Hb T (withP st p) w c.2.1 c.2.2.1) T (withP st p) c.1)) c.2) =
      pr (mainH Hb T p hm).Coins (fun k => D ((mainH Hb T p hm).fillS.out (some (st, w)) k)
        (visOf Hb T hm ((mainH Hb T p hm).obsOf (some (st, w)) k))) := by
    rw [← pr_equiv (coinsEquiv Hb T hm)]
    refine pr_congr fun k => ?_
    show D (some (proveIdeal (recP Hb T (withP st p) w k.2.2.2.1 k.2.2.1) T (withP st p) w
      (fillSib (recP Hb T (withP st p) w k.2.2.2.1 k.2.2.1) T (withP st p) (k.1.1, withSib k.1.2 k.2.1))))
      (k.2.2.2.1, k.2.2.1, k.2.2.2.2) ↔ _
    rw [HSlot.fillS_out, mainH_out]
    erw [mainOut_fill Hb T st w k.1 k.2.1]
    exact Iff.rfl
  have eR : pr (realSlot Hb T p).K (fun k => D ((realSlot Hb T p).out (some (st, w)) k)
      ((realSlot Hb T p).obs (some (st, w)) k)) =
      pr ((Bytes 16 × Tab2) × Vis p) (fun c =>
        D' (proveE (recOf Hb T (withP st p) w (preReal Hb (withP st p) w T c.2.2.1 c.2.2.2) c.2.1 c.1.2 c.2.2.1) T (withP st p) w
          c.2.2.2 (preReal Hb (withP st p) w T c.2.2.1 c.2.2.2) c.1.1) c.2) :=
    pr_congr fun _ => Iff.rfl
  have eF : pr ((mainH Hb T p hm).fillS.mapObs (visOf Hb T hm)).K (fun k =>
      D (((mainH Hb T p hm).fillS.mapObs (visOf Hb T hm)).out (some (st, w)) k)
        (((mainH Hb T p hm).fillS.mapObs (visOf Hb T hm)).obs (some (st, w)) k)) =
      pr (mainH Hb T p hm).Coins (fun k => D ((mainH Hb T p hm).fillS.out (some (st, w)) k)
        (visOf Hb T hm ((mainH Hb T p hm).obsOf (some (st, w)) k))) :=
    pr_congr fun _ => Iff.rfl
  rw [eR, eF, ← e]
  have := abs_sub_le_iff.1 h1; have := abs_sub_le_iff.1 h2; have := abs_sub_le_iff.1 h3
  have := abs_sub_le_iff.1 h4
  rw [abs_sub_le_iff]; unfold εRF; constructor <;> linarith

/-- **The ideal tape with uniform sibling answers is the simulator** (exact, with the tables). -/
theorem ideal_sim_close (hm : MainP p) :
    Slot.Close (fun _ => True) (ValidZK T p) 0
      ((mainH Hb T p hm).idealS.mapObs (visOf Hb T hm)) (simSlot p) := by
  intro y hy D _
  rcases y with _ | ⟨st, w⟩
  · have e1 : pr (simSlot p).K (fun k => D none k.2) = pr (Vis p) (D none) :=
      pr_prod_snd (α := SimCoins p) (D none)
    have e2 := pr_vis_coins Hb T hm (D none)
    rw [abs_nonpos_iff, sub_eq_zero]
    exact e2.trans e1.symm
  obtain ⟨cs, hzk⟩ := hy (st, w) rfl
  have h := joint_sim Hb T (withP st p) w hzk (fun o v => D (some o) v)
  dsimp only [withP_params] at h
  have e : pr (IdealTape p × Vis p) (fun c => D (some (proveIdeal (recP Hb T (withP st p) w c.2.1 c.2.2.1) T
      (withP st p) w c.1)) c.2) =
      pr (mainH Hb T p hm).Coins (fun k => D ((mainH Hb T p hm).idealS.out (some (st, w)) k)
        (visOf Hb T hm ((mainH Hb T p hm).obsOf (some (st, w)) k))) := by
    rw [← pr_equiv (coinsEquiv Hb T hm)]
    refine pr_congr fun k => ?_
    show D (some (proveIdeal (recP Hb T (withP st p) w k.2.2.2.1 k.2.2.1) T (withP st p) w
      (k.1.1, withSib k.1.2 k.2.1))) (k.2.2.2.1, k.2.2.1, k.2.2.2.2) ↔ _
    rw [HSlot.idealS_out, mainH_out]
    exact Iff.rfl
  have eI : pr ((mainH Hb T p hm).idealS.mapObs (visOf Hb T hm)).K (fun k =>
      D (((mainH Hb T p hm).idealS.mapObs (visOf Hb T hm)).out (some (st, w)) k)
        (((mainH Hb T p hm).idealS.mapObs (visOf Hb T hm)).obs (some (st, w)) k)) =
      pr (mainH Hb T p hm).Coins (fun k => D ((mainH Hb T p hm).idealS.out (some (st, w)) k)
        (visOf Hb T hm ((mainH Hb T p hm).obsOf (some (st, w)) k))) :=
    pr_congr fun _ => Iff.rfl
  have eS : pr (simSlot p).K (fun k => D ((simSlot p).out (some (st, w)) k)
      ((simSlot p).obs (some (st, w)) k)) =
      pr (SimCoins p × Vis p) (fun c => D (some (simulate p c.1)) c.2) :=
    pr_congr fun _ => Iff.rfl
  rw [eI, eS, ← e]
  exact h

end Slots

end VoleMole.ZK.Sim
