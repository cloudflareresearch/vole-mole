import VoleMole.ZK.GrindNum
import VoleMole.ZK.HopsMain

/-!
# Zero knowledge on `main` with the tables shared and `H₂³` visible (one proof)

`zk_rom_ic_main` (`ZK/HopsMain.lean`) is the zero-knowledge bound on `main` (no dedicated label
rows) in the model of `zk_rom_ic`: the `H₅` table is the proof's own (its keys are the sibling
inputs of the tapes), and the distinguisher does not read `H₂³`. Here the same bound is proved in
the model of `zk_rom_ic_h23` (`ZK/HopsIC.lean`), the one the privacy games of
`Privacy/MoussakaRO.lean` and `Privacy/RatatouilleRO.lean` use with the label-row fix:

* `H₅` is a uniform table on **every** 37-byte input (`Tab5F`), `H₂³` a uniform table on every
  grinding point (`Tab2G`), `H₃` a uniform table on the proof's seed inputs, and the cipher of the
  whole BAVC and VOLE expansion a uniform table `E`: the tables that several proofs would share;
* the distinguisher sees the proof and all four tables, reads `H₃`, `H₅`, `E` adaptively at `q₃`,
  `q₅`, `q_E` keys and **`H₂³` freely**; the simulator programs `H₂³` (`simTab`).

Only H6 uses the label rows. Every other hop of `zk_rom_ic_h23` is taken unchanged
(`joint2_h1`, `joint2_prog`, `joint2_keys`: H1, grinding and programming, the programmed points;
`joint3_h4`: H4 with the cipher a table, which is hop H8 of `lean/docs/zk.md` §6 read backwards;
`joint2_tape`, `joint2_sim`), with `MainP.hlab` in place of the label-row sizes.

**H6 on `main`** (`pr_bad_mainG`, `lab_rom_hyp_sG_main`, `joint2_h6_main`). As in
`ZK/HopsMain.lean`: a read of `H₅` at a sibling input names one candidate for the label offset
`u_pre` (`guessOfG`), on `main` `u_pre = d[0..16) ⊕ w[0..16)` (`uPre_main_dB`), and the proof's
fields are uniform, so the bad event is at most the probability that `w[0..16)` lies in the
candidate set `candidatesG` computed from the simulated proof, the tables and the distinguisher's
read set. Every 37-byte read is a candidate, whatever `iv` it names: no `iv` collision term is
needed for one proof, and other proofs' reads of the same table would count as reads.

**`zk_rom_ic_h23_main`**: for a statement of `main`'s layout the advantage is at most

    q₃·2⁻¹²⁸ + Pr[GrindBad] + 221·(4607 + q_E + 4607)·2⁻¹²⁸ + Pr[mainPred2]

and `zk_rom_ic_h23_main_num` has `2⁻¹¹³` for the grinding term. `mainPred2` is the event, **in
the simulator's experiment** (simulator coins, the tables with `H₂³` programmed, the cipher), that
the witness prefix is one of the at most `q₅ + 1` candidates (`card_candidatesG_le`) named by the
distinguisher's `H₅` reads. For a prefix that is uniform and independent of the predictor's
inputs it is at most `(q₅ + 1)·2⁻¹²⁸` (`pr_mem_uniform_le`); a distinguisher that knows the prefix
makes it `1`.

**Not covered.** One proof. A game of several proofs that share these tables and the witness
prefix needs the joint hop of `Privacy/MainChain.lean` redone with shared tables: there the
candidates of one proof include the `H₅` reads of the other real proofs, and the bad event of one
proof has to be moved across the hops of the others (`lean/docs/zk.md` §4.2).
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

set_option linter.unusedSectionVars false
-- (The linter's traversal of the large product types below exceeds the recursion limit.)
set_option linter.constructorNameAsVariable false

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy
  VoleMole.ZK.IC

attribute [local instance] decEqW128

/-! ## The candidates, for any table layout of `H₅` -/

section Cand

variable [HasPrg] (Hs : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)
  (cs : ByteArray → ByteArray → System GF128)
  {K : Type} [Fintype K] [DecidableEq K] (enc : K → ByteArray)

/-- **The candidates for `u_pre`** from a set `S` of `H₅` table keys (any layout): zero (the
prover's own reads) and each key's guess (`guessOfG`). -/
noncomputable def guessSetG (S : Finset K) (s : Shared) (f : SimFields st.params) : Finset W128 :=
  insert W128.zero (S.biUnion (guessOfG Hs T st enc s f))

lemma guessesG_eq (QD : Except String ByteArray → (K → Bytes 4) → Finset K) (G : K → Bytes 4)
    (s : Shared) (f : SimFields st.params) :
    guessesG Hs T st enc QD G s f = guessSetG Hs T st enc (QD (outOf st s f) G) s f := rfl

lemma card_guessSetG_le (S : Finset K) (s : Shared) (f : SimFields st.params) :
    (guessSetG Hs T st enc S s f).card ≤ S.card + 1 := by
  unfold guessSetG
  refine (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ?_)
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ k ∈ S, (guessOfG Hs T st enc s f k).card ≤ ∑ _k ∈ S, 1 :=
        Finset.sum_le_sum fun k _ => card_guessOfG_le Hs T st enc s f k
    _ = S.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]

/-- **The candidate set of the witness prefix** (any layout): the 16-byte values `r` with
`thetaMain d r` a candidate for `u_pre`, `d` the fields' `d[0..16)`. -/
noncomputable def candidatesG (hm : MainP st.params) (S : Finset K) (s : Shared)
    (f : SimFields st.params) : Finset (Bytes 16) :=
  univ.filter fun r => thetaMain (pre16 hm.hw f.2.2.2.1) r ∈ guessSetG Hs T st enc S s f

lemma mem_candidatesG (hm : MainP st.params) {S : Finset K} {s : Shared}
    {f : SimFields st.params} {r : Bytes 16} :
    r ∈ candidatesG Hs T st enc hm S s f ↔
      thetaMain (pre16 hm.hw f.2.2.2.1) r ∈ guessSetG Hs T st enc S s f := by
  unfold candidatesG
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

/-- **At most `|S| + 1` candidates.** -/
lemma card_candidatesG_le (hm : MainP st.params) (S : Finset K) (s : Shared)
    (f : SimFields st.params) : (candidatesG Hs T st enc hm S s f).card ≤ S.card + 1 := by
  refine le_trans ?_ (card_guessSetG_le Hs T st enc S s f)
  refine Finset.card_le_card_of_injOn (thetaMain (pre16 hm.hw f.2.2.2.1)) (fun r hr => ?_)
    (fun r _ r' _ h => thetaMain_injective _ h)
  rw [mem_coe, mem_candidatesG] at hr
  exact hr

/-- The candidates do not depend on the hashes of an unread domain. -/
lemma candidatesG_agreeOff {k : Kind} {Hs Hs' : Hashes} (hu : Unread k) (h : Hs.AgreeOff k Hs') :
    candidatesG Hs T st enc = candidatesG Hs' T st enc := by
  have hP := h.pubOf' hu st
  have hg : guessOfG Hs T st enc = guessOfG Hs' T st enc := by
    funext s f k
    unfold guessOfG qcolsF
    rw [hP]
  funext hm S s f
  unfold candidatesG guessSetG
  rw [hg]

end Cand

/-! ## H6 on `main`, for any table layout -/

section H6

variable [HasPrg] (Hs : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)
  (cs : ByteArray → ByteArray → System GF128)
  {K : Type} [Fintype K] [DecidableEq K] (enc : K → ByteArray)
  (sk : Shared × PadsU st.params → Fin 312 → K)

set_option synthInstance.maxSize 1024 in
/-- **For a fixed shared tape and table, the bad event is a prediction** of `w[0..16)` from the
uniform fields (`pr_bad_main` for any layout). -/
theorem pr_bad_mainG
    (hsk : ∀ c e, enc (sk c e) = sibInput Hs T st c.1 (withSib c.2 fun _ => fun _ => 0) e)
    (hm : MainP st.params) (h : ZKHyp T st w cs)
    (QD : Except String ByteArray → (K → Bytes 4) → Finset K) (G : K → Bytes 4) (s : Shared) :
    pr (Pads st.params) (fun t => ∃ e, sk (s, dropSib t) e ∈
      proverKeysG Hs T st enc (s, t) ∪ QD (proveIdeal (Hs.withTable .h5 enc G) T st w (s, t)) G) ≤
      pr (SimFields st.params) (fun f =>
        wPre w ∈ candidatesG Hs T st enc hm (QD (outOf st s f) G) s f) := by
  let F := fieldsOf (Hs.withTable .h5 enc G) T st w cs s (hitOf s).1 (hitOf s).2
  let Ev : SimFields st.params → Prop := fun f =>
    wPre w ∈ candidatesG Hs T st enc hm (QD (outOf st s f) G) s f
  have e1 : pr (Pads st.params) (fun t => ∃ e, sk (s, dropSib t) e ∈
      proverKeysG Hs T st enc (s, t) ∪ QD (proveIdeal (Hs.withTable .h5 enc G) T st w (s, t)) G) ≤
      pr (Pads st.params) (fun t => Ev (F t).1) := by
    refine pr_mono fun t ht => ?_
    have hm' := bad_mem_guessesG Hs T st w cs enc sk QD hsk hm.hlab h G s t ht
    rw [uPre_main_dB hm w t, guessesG_eq] at hm'
    show wPre w ∈ candidatesG Hs T st enc hm _ s (F t).1
    rw [mem_candidatesG]
    exact hm'
  have e2 : pr (Pads st.params) (fun t => Ev (F t).1) =
      pr (SimFields st.params × Bytes (labelBytes st.params)) (fun y => Ev y.1) := by
    have := (upush_fieldsOf (Hs.withTable .h5 enc G) T st w cs s (hitOf s).1 (hitOf s).2 h.hT
      h.hnm) (fun y => Ev y.1)
    rw [abs_nonpos_iff, sub_eq_zero] at this
    exact this
  rw [e2, pr_prod_fst] at e1
  exact e1

set_option synthInstance.maxSize 1024 in
/-- **H6 on `main` in the ROM, for a distinguisher that also reads the shared tape**
(`lab_rom_hyp_sG` with the bad event bounded by a prediction): any table layout of `H₅`. -/
theorem lab_rom_hyp_sG_main
    (hsk : ∀ c e, enc (sk c e) = sibInput Hs T st c.1 (withSib c.2 fun _ => fun _ => 0) e)
    (hkey : ∀ c e, keyOf enc (sk c e) = sk c e)
    (hm : MainP st.params) (h : ZKHyp T st w cs)
    (D : Except String ByteArray → Shared → (K → Bytes 4) → Prop)
    (QD : Except String ByteArray → Shared → (K → Bytes 4) → Finset K)
    (hA : ∀ (t : IdealTape st.params) G G', (∀ k ∈ proverKeysG Hs T st enc t ∪
        QD (proveIdeal (Hs.withTable .h5 enc G) T st w t) t.1 G, G k = G' k) →
      (D (proveIdeal (Hs.withTable .h5 enc G) T st w t) t.1 G ↔
        D (proveIdeal (Hs.withTable .h5 enc G') T st w t) t.1 G')) :
    |pr (IdealTape st.params × (K → Bytes 4)) (fun x =>
        D (proveIdeal (Hs.withTable .h5 enc x.2) T st w (fillSib (Hs.withTable .h5 enc x.2) T st x.1))
          x.1.1 x.2) -
      pr (IdealTape st.params × (K → Bytes 4))
        (fun x => D (proveIdeal (Hs.withTable .h5 enc x.2) T st w x.1) x.1.1 x.2)| ≤
      pr ((Shared × SimFields st.params) × (K → Bytes 4)) (fun x =>
        wPre w ∈ candidatesG Hs T st enc hm (QD (outOf st x.1.1 x.1.2) x.1.1 x.2) x.1.1 x.1.2) := by
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
      D (proveIdeal (Hs.withTable .h5 enc x.2) T st w (fillSib (Hs.withTable .h5 enc x.2) T st x.1))
        x.1.1 x.2) =
      pr ((Shared × PadsU st.params) × (K → Bytes 4)) (fun x =>
        D (proveIdeal (Hs.withTable .h5 enc x.2) T st w (fillSib (Hs.withTable .h5 enc x.2) T st
          (x.1.1, withSib x.1.2 fun _ => fun _ => 0))) x.1.1 x.2) := by
    rw [← pr_equiv E2, ← pr_prod_fst (β := Sib) (fun x : (Shared × PadsU st.params) ×
      (K → Bytes 4) => D (proveIdeal (Hs.withTable .h5 enc x.2) T st w
        (fillSib (Hs.withTable .h5 enc x.2) T st (x.1.1, withSib x.1.2 fun _ => fun _ => 0)))
        x.1.1 x.2)]
    refine pr_congr fun y => ?_
    show D (proveIdeal (Hs.withTable .h5 enc y.1.2) T st w (fillSib (Hs.withTable .h5 enc y.1.2) T st
        (y.1.1.1, withSib y.1.1.2 y.2))) y.1.1.1 y.1.2 ↔ _
    rw [fillSib_withSib T st _ y.1.1.1 y.1.1.2 y.2 fun _ => fun _ => 0]
  have e2 : pr (IdealTape st.params × (K → Bytes 4))
      (fun x => D (proveIdeal (Hs.withTable .h5 enc x.2) T st w x.1) x.1.1 x.2) =
      pr ((Shared × PadsU st.params) × ((K → Bytes 4) × Sib))
        (fun x => D (proveIdeal (Hs.withTable .h5 enc x.2.1) T st w (x.1.1, withSib x.1.2 x.2.2))
          x.1.1 x.2.1) :=
    (pr_equiv E3 _).symm
  rw [e1, e2]
  refine (lab_romG Hs T st enc sk hsk hkey
    (fun t G => D (proveIdeal (Hs.withTable .h5 enc G) T st w t) t.1 G)
    (fun t G => proverKeysG Hs T st enc t ∪ QD (proveIdeal (Hs.withTable .h5 enc G) T st w t) t.1 G)
    fun t G G' hG => hA t G G' hG).trans ?_
  let E : (K → Bytes 4) × IdealTape st.params ≃
      (Shared × PadsU st.params) × ((K → Bytes 4) × Sib) :=
    { toFun := fun y => ((y.2.1, dropSib y.2.2), (y.1, y.2.2.2.2.2.2.2.2))
      invFun := fun x => (x.2.1, (x.1.1, withSib x.1.2 x.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let E' : (K → Bytes 4) × (Shared × SimFields st.params) ≃
      (Shared × SimFields st.params) × (K → Bytes 4) := Equiv.prodComm _ _
  rw [← pr_equiv E, ← pr_equiv E']
  refine pr_prod_le_prod _ _ fun G => pr_prod_le_prod _ _ fun s => ?_
  exact pr_bad_mainG Hs T st w cs enc sk hsk hm h (fun o G => QD o s G) G s

end H6

/-! ## The chain, with the `H₂³` table visible -/

section Chain

variable [HasPrg] (Hb : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)

/-- **The predictor of `zk_rom_ic_h23_main`**, on the simulator's experiment: with the simulator's
coins `c.1` and the tables `c.2 = (G3, G2, G5)` (and the PRG of the instance), the witness prefix
`r` lies in the candidate set of the `H₅` keys `Q5` that the distinguisher reads on the simulated
proof and the programmed `H₂³` table. Nothing here depends on the witness but `r`. -/
def mainPred2 (hm : MainP st.params)
    (Q5 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Finset (Bytes 37))
    (r : Bytes 16) (c : SimCoins st.params × Vis2 st.params) : Prop :=
  r ∈ candidatesG Hb T st enc5 hm
    (Q5 (simulate st.params c.1) c.2.1
      (simTab Hb T st c.2.2.2 (simulate st.params c.1) c.1.1.2.1 c.2.2.1) c.2.2.2) c.1.1 c.1.2

set_option synthInstance.maxSize 1024 in
/-- **H6 on `main` with the tables** (`joint2_h6` with the bad event the prediction `mainPred2`):
the sibling answers recomputed from the `H₅` table against uniform ones, for a distinguisher that
reads the `H₅` table at the keys `Q5` and sees the other tables and the programmed `H₂³` table. -/
theorem joint2_h6_main {cs : ByteArray → ByteArray → System GF128} (hm : MainP st.params)
    (hzk : ZKHyp T st w cs) (hHb : HashesWF Hb)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Prop)
    (Q5 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F →
      Finset (Bytes 37))
    (hQ5 : ∀ o G3 G2 G5 G5', (∀ k ∈ Q5 o G3 G2 G5, G5 k = G5' k) →
      (D o G3 G2 G5 ↔ D o G3 G2 G5')) :
    |pr (IdealTape st.params × Vis2 st.params) (fun c =>
        Dp Hb T st D (proveIdeal (recB Hb st w c.2.1 c.2.2.2) T st w
          (fillSib (recB Hb st w c.2.1 c.2.2.2) T st c.1)) c.1.1.2.1 c.2) -
      pr (IdealTape st.params × Vis2 st.params) (fun c =>
        Dp Hb T st D (proveIdeal (recB Hb st w c.2.1 c.2.2.2) T st w c.1) c.1.1.2.1 c.2)| ≤
      pr (SimCoins st.params × Vis2 st.params) (mainPred2 Hb T st hm Q5 (wPre w)) := by
  have hlab := hm.hlab
  let E6 : (Tab3 × Tab2G st.params) × (IdealTape st.params × Tab5F) ≃
      IdealTape st.params × Vis2 st.params :=
    { toFun := fun c => (c.2.1, (c.1.1, (c.1.2, c.2.2)))
      invFun := fun c => ((c.2.1, c.2.2.1), (c.1, c.2.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let E7 : (Tab3 × Tab2G st.params) × ((Shared × SimFields st.params) × Tab5F) ≃
      SimCoins st.params × Vis2 st.params :=
    { toFun := fun c => (c.2.1, (c.1.1, (c.1.2, c.2.2)))
      invFun := fun c => ((c.2.1, c.2.2.1), (c.1, c.2.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv E6, ← pr_equiv E6, ← pr_equiv E7]
  refine abs_pr_prod_sub_le_pr _ _ _ fun a => ?_
  obtain ⟨G3, G2⟩ := a
  set base := (Hb.withTable .h3 (seedInput (st.mu1 Hb) (w.extract 0 st.params.witnessBytes)) G3
    ).withTable .h23 (enc2 st.params) (fun _ => 0) with hbase
  have a1 := Hb.agreeOff_withTable .h3 (seedInput (st.mu1 Hb) (w.extract 0 st.params.witnessBytes)) G3
  have a2 := (Hb.withTable .h3 (seedInput (st.mu1 Hb) (w.extract 0 st.params.witnessBytes)) G3
    ).agreeOff_withTable .h23 (enc2 st.params) (fun _ => 0)
  have hbwf : HashesWF base := (hHb.withTable .h3 _ G3).withTable .h23 _ _
  -- The layout of the table on every 37-byte input, over `base`.
  let sk : Shared × PadsU st.params → Fin 312 → Bytes 37 := fun c e =>
    blk 37 (sibInput base T st c.1 (withSib c.2 fun _ => fun _ => 0) e)
  have hsk : ∀ c e, enc5 (sk c e) = sibInput base T st c.1 (withSib c.2 fun _ => fun _ => 0) e :=
    fun c e => ba_blk_of_size (sibInput_size base T st hbwf _ _ e)
  have hkey : ∀ c e, keyOf enc5 (sk c e) = sk c e :=
    fun c e => keyOf_eq (fun a b h => ba_injective h) _
  have hv5 : ∀ G : Tab5F, vIn5 (rec5 Hb G) T st = vIn5 base T st := by
    intro G
    have a0 := Hb.agreeOff_withTable .h5 enc5 G
    refine vIn5_congr T st ?_ ?_
    · exact (a0.mu1 (by decide) (by decide) st).symm.trans
        ((a1.mu1 (by decide) (by decide) st).trans (a2.mu1 (by decide) (by decide) st))
    · exact (a0 .h4 (by decide)).symm.trans ((a1 .h4 (by decide)).trans (a2 .h4 (by decide)))
  have hA : ∀ (t : IdealTape st.params) (G G' : Tab5F), (∀ k ∈ proverKeysG base T st enc5 t ∪
      (fun o (s : Shared) G5 => Q5 o G3 (simTab Hb T st G5 o s.2.1 G2) G5)
        (proveIdeal (base.withTable .h5 enc5 G) T st w t) t.1 G, G k = G' k) →
      ((fun o (s : Shared) G5 => Dp Hb T st D o s.2.1 (G3, G2, G5))
          (proveIdeal (base.withTable .h5 enc5 G) T st w t) t.1 G ↔
        (fun o (s : Shared) G5 => Dp Hb T st D o s.2.1 (G3, G2, G5))
          (proveIdeal (base.withTable .h5 enc5 G') T st w t) t.1 G') := by
    intro t G G' hG
    have hp := proveIdeal_table_congrG base T st w enc5 hlab t G G'
      fun k hk => hG k (Finset.mem_union_left _ hk)
    have hpre : outPre Hb T st G (proveIdeal (base.withTable .h5 enc5 G) T st w t) =
        outPre Hb T st G' (proveIdeal (base.withTable .h5 enc5 G) T st w t) := by
      rcases ho : proveIdeal (base.withTable .h5 enc5 G) T st w t with e | b
      · rfl
      · simp only [outPre]
        have hag : (rec5 Hb G).AgreeOff .h5 (rec5 Hb G') :=
          Hashes.AgreeOff.withTable_same (k := .h5) (Hs := Hb) (Hs' := Hb) (fun _ _ => rfl) enc5
            enc5 G G'
        refine vPre_h5_congr hag T st b fun x hx => ?_
        rw [hv5] at hx
        have hx' : x ∈ actInputs base T st t.1 t.2 :=
          vIn5_proveIdeal base T st w (base.withTable .h5 enc5 G) hzk t.1 t.2 ho x hx
        simp only [rec5, Hashes.withTable, ↓reduceIte]
        split
        · rename_i hy
          have hk : hy.choose ∈ proverKeysG base T st enc5 t := by
            rw [mem_proverKeysG, hy.choose_spec]; exact hx'
          exact congrArg ba (hG _ (Finset.mem_union_left _ hk))
        · rfl
    have hX : simTab Hb T st G' (proveIdeal (base.withTable .h5 enc5 G') T st w t) t.1.2.1 G2 =
        simTab Hb T st G (proveIdeal (base.withTable .h5 enc5 G) T st w t) t.1.2.1 G2 := by
      unfold simTab
      rw [← hp, ← hpre]
    show D (proveIdeal (base.withTable .h5 enc5 G) T st w t) G3
        (simTab Hb T st G (proveIdeal (base.withTable .h5 enc5 G) T st w t) t.1.2.1 G2) G ↔
      D (proveIdeal (base.withTable .h5 enc5 G') T st w t) G3
        (simTab Hb T st G' (proveIdeal (base.withTable .h5 enc5 G') T st w t) t.1.2.1 G2) G'
    rw [hX, ← hp]
    exact hQ5 _ G3 _ G G' fun k hk => hG k (Finset.mem_union_right _ hk)
  have key := lab_rom_hyp_sG_main base T st w cs enc5 sk hsk hkey hm hzk
    (fun o (s : Shared) G5 => Dp Hb T st D o s.2.1 (G3, G2, G5))
    (fun o (s : Shared) G5 => Q5 o G3 (simTab Hb T st G5 o s.2.1 G2) G5) hA
  refine key.trans (le_of_eq (pr_congr fun x => ?_))
  have b1 : base.AgreeOff .h23 (Hb.withTable .h3 (seedInput (st.mu1 Hb)
      (w.extract 0 st.params.witnessBytes)) G3) := a2.symm
  have b2 : (Hb.withTable .h3 (seedInput (st.mu1 Hb)
      (w.extract 0 st.params.witnessBytes)) G3).AgreeOff .h3 Hb := a1.symm
  show _ ↔ mainPred2 Hb T st hm Q5 (wPre w) (x.1, (G3, (G2, x.2)))
  unfold mainPred2
  rw [candidatesG_agreeOff T st enc5 unread_h23 b1, candidatesG_agreeOff T st enc5 unread_h3 b2,
    simulate_eq_outOf]

end Chain

/-! ## The chain around H4, for any PRG -/

section Generic

variable [HasPrg] (Hb : Hashes) (st : Statement) (w : ByteArray)

/-- **The hybrids before H4 on `main`** (`zk_pre_h4`, which uses the label rows only through
`labelRowOffset + 128 ≤ correctionRows`). -/
theorem zk_pre_h4_main {cs : ByteArray → ByteArray → System GF128} (hm : MainP st.params)
    (hzk : ZKHyp CrtGen.tables st w cs) (hHb : HashesWF Hb)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Prop)
    (Q3 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G2 G5, (∀ k ∈ Q3 o G3 G2 G5, G3 k = G3' k) →
      (D o G3 G2 G5 ↔ D o G3' G2 G5))
    {q3 : ℕ} (hq3 : ∀ o G3 G2 G5, (Q3 o G3 G2 G5).card ≤ q3) :
    |pr ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) (fun c =>
        D (Prover.prove (recH Hb st w c.2.1 c.1.2 c.2.2) CrtGen.tables st w (ba c.1.1))
          c.2.1 c.1.2 c.2.2) -
      pr (((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5F)) (fun c =>
        Dp Hb CrtGen.tables st D (hyb3 (recB Hb st w c.2.1 c.2.2) CrtGen.tables st w
          (c.1.1.2, c.1.2.2)
          (hiddenOut st.params (ivOfPre Hb st c.1.1.2) (ba (deltaOf c.1.2.2)) c.1.1.1))
          c.1.2.2 (c.2.1, c.1.2.1, c.2.2))| ≤
      q3 / 2 ^ 128 + pr Grind (GrindBad CrtGen.tables) := by
  have hlab := hm.hlab
  have e0 : pr ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) (fun c =>
      D (Prover.prove (recH Hb st w c.2.1 c.1.2 c.2.2) CrtGen.tables st w (ba c.1.1))
        c.2.1 c.1.2 c.2.2) =
      pr ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) (fun c =>
        D (proveP (recH Hb st w c.2.1 c.1.2 c.2.2) CrtGen.tables st w
          (preR Hb CrtGen.tables st w c.2.2) c.1.1) c.2.1 c.1.2 c.2.2) := by
    refine pr_congr fun c => ?_
    have hR : RunHyp (recH Hb st w c.2.1 c.1.2 c.2.2) CrtGen.tables st w cs :=
      ⟨hzk, recH_wf hHb _ _ _, bavcComplete, fun rho => crtComplete _ _ _ _ rho _ hlab, hlab⟩
    rw [← proveP_prove _ CrtGen.tables st w hR c.1.1, prePrefix_recH]
  rw [e0]
  have h1 := joint2_h1 Hb CrtGen.tables st w D Q3 hQ3 hq3
  have h2 := joint2_prog Hb CrtGen.tables st w hHb hzk.q D
  have h3 := joint2_keys Hb st w hHb hzk hlab D
  have := abs_sub_le _ _ _ |>.trans (add_le_add h1 ((abs_sub_le _ _ _).trans (add_le_add h2 h3)))
  exact this.trans (le_of_eq (by ring))

/-- **The hybrids after H4 on `main`** (the tape, H6 on `main`, the simulator), for any PRG. -/
theorem zk_post_h4_main {cs : ByteArray → ByteArray → System GF128} (hm : MainP st.params)
    (hzk : ZKHyp CrtGen.tables st w cs) (hHb : HashesWF Hb)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Prop)
    (Q5 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F →
      Finset (Bytes 37))
    (hQ5 : ∀ o G3 G2 G5 G5', (∀ k ∈ Q5 o G3 G2 G5, G5 k = G5' k) →
      (D o G3 G2 G5 ↔ D o G3 G2 G5')) :
    |pr ((Hidden st.params × (Bytes 16 × Grind)) × Vis2 st.params) (fun c =>
        Dp Hb CrtGen.tables st D (hyb3 (recB Hb st w c.2.1 c.2.2.2) CrtGen.tables st w
          c.1.2 (hiddenIdeal (ba (deltaOf c.1.2.2)) c.1.1)) c.1.2.2 c.2) -
      pr (SimCoins st.params × Vis2 st.params) (fun c =>
        D (simulate st.params c.1) c.2.1
          (simTab Hb CrtGen.tables st c.2.2.2 (simulate st.params c.1) c.1.1.2.1 c.2.2.1) c.2.2.2)| ≤
      pr (SimCoins st.params × Vis2 st.params)
        (mainPred2 Hb CrtGen.tables st hm Q5 (wPre w)) := by
  have h5 := joint2_tape Hb CrtGen.tables st w D
  have h6 := joint2_h6_main Hb CrtGen.tables st w hm hzk hHb D Q5 hQ5
  have h7 := joint2_sim Hb CrtGen.tables st w hzk D
  have := abs_sub_le _ _ _ |>.trans (add_le_add h5 ((abs_sub_le _ _ _).trans (add_le_add h6 h7)))
  exact this.trans (le_of_eq (by ring))

end Generic

/-! ## The end-to-end statement -/

section Main

variable (Hb : Hashes) (st : Statement) (w : ByteArray)

/-- **The predictor in the ideal-cipher model**: `mainPred2` with the PRG of the cipher table and
the distinguisher's read set at that table, on the simulator's experiment
`(simulator coins, tables) × cipher`. -/
def mainPredIC (hm : MainP st.params)
    (Q5 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset (Bytes 37))
    (r : Bytes 16) (c : (SimCoins st.params × Vis2 st.params) × Cipher) : Prop :=
  @mainPred2 (icPrg c.2) Hb CrtGen.tables st hm (fun o G3 G2 G5 => Q5 o G3 G2 G5 c.2) r c.1

/-- **Zero knowledge on `main` in the random-oracle and ideal-cipher model with `H₂³` visible**
(no label rows, faest-arch-opt's tables, one statement and witness). The experiment is that of
`zk_rom_ic_h23`: the executable prover with the ideal-cipher PRG `icPrg E` and the record
`recH Hb … G3 G2 G5` (`H₃`, `H₂³`, `H₅` uniform tables, `H₅` on every 37-byte input), against the
simulator `simulate` with the programmed table `simTab`; the distinguisher sees the output and all
tables, reads `H₃`, `H₅`, `E` at the keys `Q3`, `Q5`, `QE` (`q₃`, `q_E` bound the first and the
last) and `H₂³` freely. For a statement of `main`'s layout (`MainP`) its advantage is at most

    q₃·2⁻¹²⁸ + Pr[GrindBad] + 221·(4607 + q_E + 4607)·2⁻¹²⁸ + Pr[mainPredIC]

where `Pr[mainPredIC]` is the probability, in the simulator's experiment, that the witness prefix
`w[0..16)` is one of the candidates named by the distinguisher's `H₅` reads (`card_candidatesG_le`:
at most `|Q5| + 1` of them). -/
theorem zk_rom_ic_h23_main {cs : ByteArray → ByteArray → System GF128} (hm : MainP st.params)
    (hzk : ZKHyp CrtGen.tables st w cs) (hHb : HashesWF Hb) (hp : SmallParams st.params)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Prop)
    (Q3 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G2 G5 E, (∀ k ∈ Q3 o G3 G2 G5 E, G3 k = G3' k) →
      (D o G3 G2 G5 E ↔ D o G3' G2 G5 E))
    {q3 : ℕ} (hq3 : ∀ o G3 G2 G5 E, (Q3 o G3 G2 G5 E).card ≤ q3)
    (Q5 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset (Bytes 37))
    (hQ5 : ∀ o G3 G2 G5 G5' E, (∀ k ∈ Q5 o G3 G2 G5 E, G5 k = G5' k) →
      (D o G3 G2 G5 E ↔ D o G3 G2 G5' E))
    (QE : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset Blk)
    (hQE : ∀ o G3 G2 G5 E E', (∀ k ∈ QE o G3 G2 G5 E, E k = E' k) →
      (D o G3 G2 G5 E ↔ D o G3 G2 G5 E'))
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 E, (QE o G3 G2 G5 E).card ≤ qE) :
    |pr (((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × Cipher) (fun c =>
        D (@Prover.prove (icPrg c.2) (recH Hb st w c.1.2.1 c.1.1.2 c.1.2.2) CrtGen.tables st w
          (ba c.1.1.1) st.params.witnessBytes) c.1.2.1 c.1.1.2 c.1.2.2 c.2) -
      pr ((SimCoins st.params × Vis2 st.params) × Cipher) (fun c =>
        D (simulate st.params c.1.1) c.1.2.1
          (@simTab (icPrg c.2) Hb CrtGen.tables st c.1.2.2.2 (simulate st.params c.1.1) c.1.1.1.2.1
            c.1.2.2.1) c.1.2.2.2 c.2)| ≤
      q3 / 2 ^ 128 + pr Grind (GrindBad CrtGen.tables) + 221 * (4607 + (qE + 4607)) / 2 ^ 128 +
        pr ((SimCoins st.params × Vis2 st.params) × Cipher)
          (mainPredIC Hb st hm Q5 (wPre w)) := by
  have hA := abs_pr_avgE
    (fun (c : (Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) (E : Cipher) =>
      D (@Prover.prove (icPrg E) (recH Hb st w c.2.1 c.1.2 c.2.2) CrtGen.tables st w (ba c.1.1)
        st.params.witnessBytes) c.2.1 c.1.2 c.2.2 E)
    (fun (c : ((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5F)) (E : Cipher) =>
      @Dp (icPrg E) Hb CrtGen.tables st (fun o G3 G2 G5 => D o G3 G2 G5 E)
        (@hyb3 (icPrg E) (recB Hb st w c.2.1 c.2.2) CrtGen.tables st w (c.1.1.2, c.1.2.2)
          (@hiddenOut (icPrg E) st.params (ivOfPre Hb st c.1.1.2) (ba (deltaOf c.1.2.2)) c.1.1.1))
        c.1.2.2 (c.2.1, c.1.2.1, c.2.2))
    (fun E => @zk_pre_h4_main (icPrg E) Hb st w cs hm hzk hHb (fun o G3 G2 G5 => D o G3 G2 G5 E)
      (fun o G3 G2 G5 => Q3 o G3 G2 G5 E) (fun o G3 G3' G2 G5 => hQ3 o G3 G3' G2 G5 E) q3
      (fun o G3 G2 G5 => hq3 o G3 G2 G5 E))
  have hB := joint3_h4 Hb CrtGen.tables st w hp hzk D QE hQE hqE
  have hC := abs_pr_prod_sub_le_pr'
    (fun (c : ((Hidden st.params × (Bytes 16 × Grind)) × Vis2 st.params) × Cipher) =>
      @Dp (icPrg c.2) Hb CrtGen.tables st (fun o G3 G2 G5 => D o G3 G2 G5 c.2)
        (@hyb3 (icPrg c.2) (recB Hb st w c.1.2.1 c.1.2.2.2) CrtGen.tables st w c.1.1.2
          (hiddenIdeal (ba (deltaOf c.1.1.2.2)) c.1.1.1)) c.1.1.2.2 c.1.2)
    (fun (c : (SimCoins st.params × Vis2 st.params) × Cipher) =>
      D (simulate st.params c.1.1) c.1.2.1
        (@simTab (icPrg c.2) Hb CrtGen.tables st c.1.2.2.2 (simulate st.params c.1.1) c.1.1.1.2.1
          c.1.2.2.1) c.1.2.2.2 c.2)
    (mainPredIC Hb st hm Q5 (wPre w))
    (fun E => @zk_post_h4_main (icPrg E) Hb st w cs hm hzk hHb (fun o G3 G2 G5 => D o G3 G2 G5 E)
      (fun o G3 G2 G5 => Q5 o G3 G2 G5 E) (fun o G3 G2 G5 G5' => hQ5 o G3 G2 G5 G5' E))
  refine (abs_sub_le _ _ _).trans ((add_le_add hA ((abs_sub_le _ _ _).trans
    (add_le_add hB hC))).trans (le_of_eq (by ring)))

/-- **`zk_rom_ic_h23_main` with the grinding term numeric**: on `main`, the executable prover is

    q₃·2⁻¹²⁸ + 2⁻¹¹³ + 221·(4607 + q_E + 4607)·2⁻¹²⁸ + Pr[mainPredIC]

close to the programming simulator, against a distinguisher that reads `H₃`, `E` at `q₃`, `q_E`
keys, `H₅` at the keys `Q5` and `H₂³` freely. -/
theorem zk_rom_ic_h23_main_num {cs : ByteArray → ByteArray → System GF128} (hm : MainP st.params)
    (hzk : ZKHyp CrtGen.tables st w cs) (hHb : HashesWF Hb) (hp : SmallParams st.params)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Prop)
    (Q3 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G2 G5 E, (∀ k ∈ Q3 o G3 G2 G5 E, G3 k = G3' k) →
      (D o G3 G2 G5 E ↔ D o G3' G2 G5 E))
    {q3 : ℕ} (hq3 : ∀ o G3 G2 G5 E, (Q3 o G3 G2 G5 E).card ≤ q3)
    (Q5 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset (Bytes 37))
    (hQ5 : ∀ o G3 G2 G5 G5' E, (∀ k ∈ Q5 o G3 G2 G5 E, G5 k = G5' k) →
      (D o G3 G2 G5 E ↔ D o G3 G2 G5' E))
    (QE : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset Blk)
    (hQE : ∀ o G3 G2 G5 E E', (∀ k ∈ QE o G3 G2 G5 E, E k = E' k) →
      (D o G3 G2 G5 E ↔ D o G3 G2 G5 E'))
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 E, (QE o G3 G2 G5 E).card ≤ qE) :
    |pr (((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × Cipher) (fun c =>
        D (@Prover.prove (icPrg c.2) (recH Hb st w c.1.2.1 c.1.1.2 c.1.2.2) CrtGen.tables st w
          (ba c.1.1.1) st.params.witnessBytes) c.1.2.1 c.1.1.2 c.1.2.2 c.2) -
      pr ((SimCoins st.params × Vis2 st.params) × Cipher) (fun c =>
        D (simulate st.params c.1.1) c.1.2.1
          (@simTab (icPrg c.2) Hb CrtGen.tables st c.1.2.2.2 (simulate st.params c.1.1) c.1.1.1.2.1
            c.1.2.2.1) c.1.2.2.2 c.2)| ≤
      q3 / 2 ^ 128 + 1 / 2 ^ 113 + 221 * (4607 + (qE + 4607)) / 2 ^ 128 +
        pr ((SimCoins st.params × Vis2 st.params) × Cipher)
          (mainPredIC Hb st hm Q5 (wPre w)) :=
  (zk_rom_ic_h23_main Hb st w hm hzk hHb hp D Q3 hQ3 hq3 Q5 hQ5 QE hQE hqE).trans
    (add_le_add (add_le_add (add_le_add le_rfl grindBad_le_113) le_rfl) le_rfl)

/-- **The predictor's candidate set** for the witness prefix, on the simulator's experiment
(`mainPredIC … r c ↔ r ∈ candIC … c`, by definition). -/
noncomputable def candIC (hm : MainP st.params)
    (Q5 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset (Bytes 37))
    (c : (SimCoins st.params × Vis2 st.params) × Cipher) : Finset (Bytes 16) :=
  letI : HasPrg := icPrg c.2
  candidatesG Hb CrtGen.tables st enc5 hm
    (Q5 (simulate st.params c.1.1) c.1.2.1
      (simTab Hb CrtGen.tables st c.1.2.2.2 (simulate st.params c.1.1) c.1.1.1.2.1
        c.1.2.2.1) c.1.2.2.2 c.2) c.1.1.1 c.1.1.2

lemma mainPredIC_iff (hm : MainP st.params)
    (Q5 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset (Bytes 37))
    (r : Bytes 16) (c : (SimCoins st.params × Vis2 st.params) × Cipher) :
    mainPredIC Hb st hm Q5 r c ↔ r ∈ candIC Hb st hm Q5 c := Iff.rfl

/-- **The predictor names at most `q₅ + 1` candidates** for the witness prefix. -/
theorem card_candIC_le (hm : MainP st.params)
    (Q5 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset (Bytes 37))
    {q5 : ℕ} (hq5 : ∀ o G3 G2 G5 E, (Q5 o G3 G2 G5 E).card ≤ q5)
    (c : (SimCoins st.params × Vis2 st.params) × Cipher) :
    (candIC Hb st hm Q5 c).card ≤ q5 + 1 := by
  let _ : HasPrg := icPrg c.2
  exact (card_candidatesG_le Hb CrtGen.tables st enc5 hm _ c.1.1.1 c.1.1.2).trans
    (Nat.succ_le_succ (hq5 _ _ _ _ _))

/-- **A uniform prefix** (the statistical case of (PU)): if the witness prefix `r` is uniform and
independent of the predictor's inputs, the (PU) term is at most `(q₅ + 1)·2⁻¹²⁸`, the label-row
term of `zk_rom_ic_h23`. -/
theorem pr_mainPredIC_uniform_le (hm : MainP st.params)
    (Q5 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset (Bytes 37))
    {q5 : ℕ} (hq5 : ∀ o G3 G2 G5 E, (Q5 o G3 G2 G5 E).card ≤ q5) :
    pr (Bytes 16 × ((SimCoins st.params × Vis2 st.params) × Cipher))
      (fun z => mainPredIC Hb st hm Q5 z.1 z.2) ≤ (q5 + 1) / 2 ^ 128 :=
  pr_mem_uniform_le (candIC Hb st hm Q5) fun c => card_candIC_le Hb st hm Q5 hq5 c

end Main

end VoleMole.ZK.Sim
