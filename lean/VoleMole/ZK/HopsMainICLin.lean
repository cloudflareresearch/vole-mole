import VoleMole.ZK.MainSharedSlots

/-!
# Zero knowledge on `main` for one proof, identical until bad (`lean/docs/zk.md` §4.2)

`zk_rom_ic_h23_main` (`ZK/HopsMainIC.lean`) bounds the advantage of a distinguisher `D` by
`εS + Pr_sim[mainPredIC]`: the hops H1–H4 and the tape steps cost `εS` for every `D`, and H6 (the
sibling answers of `H₅` read from the table against uniform ones) costs the probability of the bad
event "a sibling key is read", bounded by the prediction `mainPredIC` on the simulated proof.

Here H6 is used in its **identical-until-bad** form. The two sides of H6 agree unless a sibling
key is read (`pr_hidden_eq`: the programmed and the unprogrammed table give the same law to a run
that holds whenever it reads a programmed point). A read of a sibling key on a tape implies the
prediction on the proof the ideal-tape prover outputs there, which is a simulated proof
(`proveIdeal_eq_outOf`, `bad_mem_guessesG`). So if `D` **holds on every simulated proof where the
prediction holds** (`hB`), H6 is exact, and

    |Pr[D(real)] − Pr[D(sim)]| ≤ εS(q₃, q_E)                     (zk_rom_ic_h23_main_iub)

with no (PU) term. A game of several proofs applies this to `F ∨ bad`, where `bad` is an event of
the view that contains every hop's prediction (`ZK/MainSharedLin.lean`): the bad event is then not
moved across the later hops, and the joint hop is linear in the number of proofs.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Privacy

/-- **Identical until a programmed point is read, as an equality.** If the run `A c u g` reads the
table `g` only on the keys `Q c u g` (`hQ`) and **holds whenever it reads a programmed point**
(`hB`), then reading the real answers `g ∘ x c` and reading independent answers `u` give `A` the
same probability (`abs_pr_hidden_le` with the bad event inside `A`). No consistency of `Q` is
needed. -/
theorem pr_hidden_eq {ι C K R : Type*} [Fintype K] [DecidableEq K] [Fintype R] [Fintype ι]
    [DecidableEq ι] [Fintype C] [Nonempty ι] [Nonempty R] {x : C → ι → K}
    (hx : ∀ c, Function.Injective (x c)) (A : C → (ι → R) → (K → R) → Prop)
    (Q : C → (ι → R) → (K → R) → Finset K)
    (hQ : ∀ c u g g', (∀ k ∈ Q c u g, g k = g' k) → (A c u g ↔ A c u g'))
    (hB : ∀ c u g, (∃ i, x c i ∈ Q c u g) → A c u g) :
    pr (C × (K → R)) (fun p => A p.1 (p.2 ∘ x p.1) p.2) =
      pr (C × ((K → R) × (ι → R))) (fun p => A p.1 p.2.2 p.2.1) := by
  rw [pr_program_eq hx]
  refine pr_congr fun p => ?_
  obtain ⟨c, g, u⟩ := p
  show A c u (programAt (x c) u g) ↔ A c u g
  have hoff : ∀ k, (∀ i, x c i ≠ k) → programAt (x c) u g k = g k := fun k hk =>
    programAt_apply_of_ne u g hk
  by_cases hb : ∃ i, x c i ∈ Q c u g
  · have h1 := hB c u g hb
    by_cases hb' : ∃ i, x c i ∈ Q c u (programAt (x c) u g)
    · exact iff_of_true (hB _ _ _ hb') h1
    · push Not at hb'
      exact iff_of_true ((hQ c u _ g fun k hk => hoff k fun i hi => hb' i (hi ▸ hk)).2 h1) h1
  · push Not at hb
    exact (hQ c u g _ fun k hk => (hoff k fun i hi => hb i (hi ▸ hk)).symm).symm

/-- **Equal on every fiber of the first coordinate, equal.** -/
theorem pr_prod_congr_fst {α β : Type*} [Fintype α] [Fintype β] (P Q : α × β → Prop)
    (h : ∀ a, pr β (fun b => P (a, b)) = pr β (fun b => Q (a, b))) :
    pr (α × β) P = pr (α × β) Q := by
  rw [pr_prod, pr_prod]
  congr 1
  exact Finset.sum_congr rfl fun a _ => h a

end VoleMole.Privacy

namespace VoleMole.ZK.Sim

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy
  VoleMole.ZK.IC

attribute [local instance] decEqW128

/-! ## H6 on `main`, identical until bad -/

section H6

variable [HasPrg] (Hs : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)
  (cs : ByteArray → ByteArray → System GF128)
  {K : Type} [Fintype K] [DecidableEq K] (enc : K → ByteArray)
  (sk : Shared × PadsU st.params → Fin 312 → K)

set_option synthInstance.maxSize 1024 in
/-- **`lab_romG` as an equality** for a run that holds whenever it reads a sibling key. -/
theorem lab_romG_eq
    (hsk : ∀ c e, enc (sk c e) = sibInput Hs T st c.1 (withSib c.2 fun _ => fun _ => 0) e)
    (hkey : ∀ c e, keyOf enc (sk c e) = sk c e)
    (A : IdealTape st.params → (K → Bytes 4) → Prop)
    (Q : IdealTape st.params → (K → Bytes 4) → Finset K)
    (hQ : ∀ t G G', (∀ k ∈ Q t G, G k = G' k) → (A t G ↔ A t G'))
    (hB : ∀ c u G, (∃ e, sk c e ∈ Q (c.1, withSib c.2 u) G) → A (c.1, withSib c.2 u) G) :
    pr ((Shared × PadsU st.params) × (K → Bytes 4)) (fun x =>
        A (fillSib (Hs.withTable .h5 enc x.2) T st
          (x.1.1, withSib x.1.2 fun _ => fun _ => 0)) x.2) =
      pr ((Shared × PadsU st.params) × ((K → Bytes 4) × Sib))
        (fun x => A (x.1.1, withSib x.1.2 x.2.2) x.2.1) := by
  simp only [fillSib_withTableG Hs T st enc sk hsk hkey]
  exact pr_hidden_eq (skG_injective Hs T st enc sk hsk) (fun c u G => A (c.1, withSib c.2 u) G)
    (fun c u G => Q (c.1, withSib c.2 u) G) (fun c u G G' h => hQ _ G G' h)
    (fun c u G h => hB c u G h)

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 1024 in
/-- **H6 on `main` for any table layout, identical until bad**: if the distinguisher holds on
every simulated proof whose candidate set contains the witness prefix (`hB`), the two sides of H6
are equal (`lab_rom_hyp_sG_main` without the bad term). -/
theorem lab_rom_hyp_sG_main_eq
    (hsk : ∀ c e, enc (sk c e) = sibInput Hs T st c.1 (withSib c.2 fun _ => fun _ => 0) e)
    (hkey : ∀ c e, keyOf enc (sk c e) = sk c e)
    (hm : MainP st.params) (h : ZKHyp T st w cs)
    (D : Except String ByteArray → Shared → (K → Bytes 4) → Prop)
    (QD : Except String ByteArray → Shared → (K → Bytes 4) → Finset K)
    (hA : ∀ (t : IdealTape st.params) G G', (∀ k ∈ proverKeysG Hs T st enc t ∪
        QD (proveIdeal (Hs.withTable .h5 enc G) T st w t) t.1 G, G k = G' k) →
      (D (proveIdeal (Hs.withTable .h5 enc G) T st w t) t.1 G ↔
        D (proveIdeal (Hs.withTable .h5 enc G') T st w t) t.1 G'))
    (hB : ∀ (s : Shared) (f : SimFields st.params) (G : K → Bytes 4),
      wPre w ∈ candidatesG Hs T st enc hm (QD (outOf st s f) s G) s f → D (outOf st s f) s G) :
    pr (IdealTape st.params × (K → Bytes 4)) (fun x =>
        D (proveIdeal (Hs.withTable .h5 enc x.2) T st w (fillSib (Hs.withTable .h5 enc x.2) T st x.1))
          x.1.1 x.2) =
      pr (IdealTape st.params × (K → Bytes 4))
        (fun x => D (proveIdeal (Hs.withTable .h5 enc x.2) T st w x.1) x.1.1 x.2) := by
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
  refine lab_romG_eq Hs T st enc sk hsk hkey
    (fun t G => D (proveIdeal (Hs.withTable .h5 enc G) T st w t) t.1 G)
    (fun t G => proverKeysG Hs T st enc t ∪ QD (proveIdeal (Hs.withTable .h5 enc G) T st w t) t.1 G)
    (fun t G G' hG => hA t G G' hG) fun c u G hb => ?_
  -- a sibling read is a prediction on the simulated proof the tape gives
  set t : Pads st.params := withSib c.2 u
  let F := fieldsOf (Hs.withTable .h5 enc G) T st w cs c.1 (hitOf c.1).1 (hitOf c.1).2
  have hm' := bad_mem_guessesG Hs T st w cs enc sk (fun o G => QD o c.1 G) hsk hm.hlab h G c.1 t hb
  rw [uPre_main_dB hm w t, guessesG_eq] at hm'
  have hc : wPre w ∈ candidatesG Hs T st enc hm (QD (outOf st c.1 (F t).1) c.1 G) c.1 (F t).1 := by
    rw [mem_candidatesG]
    exact hm'
  have hD := hB c.1 (F t).1 G hc
  show D (proveIdeal (Hs.withTable .h5 enc G) T st w (c.1, t)) c.1 G
  rw [proveIdeal_eq_outOf T st w cs _ h c.1 t]
  exact hD

end H6

/-! ## H6 with the tables, and the chain -/

section Chain

variable [HasPrg] (Hb : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 1024 in
/-- **H6 on `main` with the tables, identical until bad** (`joint2_h6_main` without the bad term):
for a distinguisher that holds on the simulator's experiment wherever the prediction `mainPred2`
holds (`hB`). -/
theorem joint2_h6_main_eq {cs : ByteArray → ByteArray → System GF128} (hm : MainP st.params)
    (hzk : ZKHyp T st w cs) (hHb : HashesWF Hb)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Prop)
    (Q5 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F →
      Finset (Bytes 37))
    (hQ5 : ∀ o G3 G2 G5 G5', (∀ k ∈ Q5 o G3 G2 G5, G5 k = G5' k) →
      (D o G3 G2 G5 ↔ D o G3 G2 G5'))
    (hB : ∀ c : SimCoins st.params × Vis2 st.params, mainPred2 Hb T st hm Q5 (wPre w) c →
      D (simulate st.params c.1) c.2.1
        (simTab Hb T st c.2.2.2 (simulate st.params c.1) c.1.1.2.1 c.2.2.1) c.2.2.2) :
    pr (IdealTape st.params × Vis2 st.params) (fun c =>
        Dp Hb T st D (proveIdeal (recB Hb st w c.2.1 c.2.2.2) T st w
          (fillSib (recB Hb st w c.2.1 c.2.2.2) T st c.1)) c.1.1.2.1 c.2) =
      pr (IdealTape st.params × Vis2 st.params) (fun c =>
        Dp Hb T st D (proveIdeal (recB Hb st w c.2.1 c.2.2.2) T st w c.1) c.1.1.2.1 c.2) := by
  have hlab := hm.hlab
  let E6 : (Tab3 × Tab2G st.params) × (IdealTape st.params × Tab5F) ≃
      IdealTape st.params × Vis2 st.params :=
    { toFun := fun c => (c.2.1, (c.1.1, (c.1.2, c.2.2)))
      invFun := fun c => ((c.2.1, c.2.2.1), (c.1, c.2.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv E6, ← pr_equiv E6]
  refine pr_prod_congr_fst _ _ fun a => ?_
  obtain ⟨G3, G2⟩ := a
  set base := (Hb.withTable .h3 (seedInput (st.mu1 Hb) (w.extract 0 st.params.witnessBytes)) G3
    ).withTable .h23 (enc2 st.params) (fun _ => 0) with hbase
  have a1 := Hb.agreeOff_withTable .h3 (seedInput (st.mu1 Hb) (w.extract 0 st.params.witnessBytes)) G3
  have a2 := (Hb.withTable .h3 (seedInput (st.mu1 Hb) (w.extract 0 st.params.witnessBytes)) G3
    ).agreeOff_withTable .h23 (enc2 st.params) (fun _ => 0)
  have hbwf : HashesWF base := (hHb.withTable .h3 _ G3).withTable .h23 _ _
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
  have b1 : base.AgreeOff .h23 (Hb.withTable .h3 (seedInput (st.mu1 Hb)
      (w.extract 0 st.params.witnessBytes)) G3) := a2.symm
  have b2 : (Hb.withTable .h3 (seedInput (st.mu1 Hb)
      (w.extract 0 st.params.witnessBytes)) G3).AgreeOff .h3 Hb := a1.symm
  have hB' : ∀ (s : Shared) (f : SimFields st.params) (G : Tab5F),
      wPre w ∈ candidatesG base T st enc5 hm
        ((fun o (s : Shared) G5 => Q5 o G3 (simTab Hb T st G5 o s.2.1 G2) G5) (outOf st s f) s G)
        s f →
      (fun o (s : Shared) G5 => Dp Hb T st D o s.2.1 (G3, G2, G5)) (outOf st s f) s G := by
    intro s f G hc
    rw [candidatesG_agreeOff T st enc5 unread_h23 b1, candidatesG_agreeOff T st enc5 unread_h3 b2,
      ← simulate_eq_outOf] at hc
    have := hB ((s, f), (G3, G2, G)) hc
    simp only [simulate_eq_outOf] at this
    exact this
  exact lab_rom_hyp_sG_main_eq base T st w cs enc5 sk hsk hkey hm hzk
    (fun o (s : Shared) G5 => Dp Hb T st D o s.2.1 (G3, G2, G5))
    (fun o (s : Shared) G5 => Q5 o G3 (simTab Hb T st G5 o s.2.1 G2) G5) hA hB'

/-- **The hybrids after H4 on `main`, identical until bad** (`zk_post_h4_main` without the bad
term). -/
theorem zk_post_h4_main_iub {cs : ByteArray → ByteArray → System GF128} (hm : MainP st.params)
    (hzk : ZKHyp CrtGen.tables st w cs) (hHb : HashesWF Hb)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Prop)
    (Q5 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F →
      Finset (Bytes 37))
    (hQ5 : ∀ o G3 G2 G5 G5', (∀ k ∈ Q5 o G3 G2 G5, G5 k = G5' k) →
      (D o G3 G2 G5 ↔ D o G3 G2 G5'))
    (hB : ∀ c : SimCoins st.params × Vis2 st.params,
      mainPred2 Hb CrtGen.tables st hm Q5 (wPre w) c →
      D (simulate st.params c.1) c.2.1
        (simTab Hb CrtGen.tables st c.2.2.2 (simulate st.params c.1) c.1.1.2.1 c.2.2.1) c.2.2.2) :
    |pr ((Hidden st.params × (Bytes 16 × Grind)) × Vis2 st.params) (fun c =>
        Dp Hb CrtGen.tables st D (hyb3 (recB Hb st w c.2.1 c.2.2.2) CrtGen.tables st w
          c.1.2 (hiddenIdeal (ba (deltaOf c.1.2.2)) c.1.1)) c.1.2.2 c.2) -
      pr (SimCoins st.params × Vis2 st.params) (fun c =>
        D (simulate st.params c.1) c.2.1
          (simTab Hb CrtGen.tables st c.2.2.2 (simulate st.params c.1) c.1.1.2.1 c.2.2.1) c.2.2.2)| ≤
      0 := by
  have h5 := joint2_tape Hb CrtGen.tables st w D
  have h6 := joint2_h6_main_eq Hb CrtGen.tables st w hm hzk hHb D Q5 hQ5 hB
  have h7 := joint2_sim Hb CrtGen.tables st w hzk D
  rw [h6] at h5
  have := abs_sub_le _ _ _ |>.trans (add_le_add h5 h7)
  exact this.trans (le_of_eq (by ring))

end Chain

/-! ## The end-to-end statement -/

section Main

variable (Hb : Hashes) (st : Statement) (w : ByteArray)

set_option maxRecDepth 8000 in
/-- **Zero knowledge on `main` with `H₂³` visible, identical until bad.** The experiments of
`zk_rom_ic_h23_main`; if the distinguisher `D` holds on the simulator's experiment wherever the
prediction `mainPredIC` holds (`hB`: the bad event is part of `D`), its advantage is at most

    q₃·2⁻¹²⁸ + Pr[GrindBad] + 221·(4607 + q_E + 4607)·2⁻¹²⁸,

with no (PU) term. -/
theorem zk_rom_ic_h23_main_iub {cs : ByteArray → ByteArray → System GF128} (hm : MainP st.params)
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
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 E, (QE o G3 G2 G5 E).card ≤ qE)
    (hB : ∀ c : (SimCoins st.params × Vis2 st.params) × Cipher,
      mainPredIC Hb st hm Q5 (wPre w) c →
      D (simulate st.params c.1.1) c.1.2.1
        (@simTab (icPrg c.2) Hb CrtGen.tables st c.1.2.2.2 (simulate st.params c.1.1) c.1.1.1.2.1
          c.1.2.2.1) c.1.2.2.2 c.2) :
    |pr (((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × Cipher) (fun c =>
        D (@Prover.prove (icPrg c.2) (recH Hb st w c.1.2.1 c.1.1.2 c.1.2.2) CrtGen.tables st w
          (ba c.1.1.1) st.params.witnessBytes) c.1.2.1 c.1.1.2 c.1.2.2 c.2) -
      pr ((SimCoins st.params × Vis2 st.params) × Cipher) (fun c =>
        D (simulate st.params c.1.1) c.1.2.1
          (@simTab (icPrg c.2) Hb CrtGen.tables st c.1.2.2.2 (simulate st.params c.1.1) c.1.1.1.2.1
            c.1.2.2.1) c.1.2.2.2 c.2)| ≤
      q3 / 2 ^ 128 + pr Grind (GrindBad CrtGen.tables) + 221 * (4607 + (qE + 4607)) / 2 ^ 128 := by
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
  have hB4 := joint3_h4 Hb CrtGen.tables st w hp hzk D QE hQE hqE
  have hC := abs_pr_prod_sub_le'
    (fun (c : ((Hidden st.params × (Bytes 16 × Grind)) × Vis2 st.params) × Cipher) =>
      @Dp (icPrg c.2) Hb CrtGen.tables st (fun o G3 G2 G5 => D o G3 G2 G5 c.2)
        (@hyb3 (icPrg c.2) (recB Hb st w c.1.2.1 c.1.2.2.2) CrtGen.tables st w c.1.1.2
          (hiddenIdeal (ba (deltaOf c.1.1.2.2)) c.1.1.1)) c.1.1.2.2 c.1.2)
    (fun (c : (SimCoins st.params × Vis2 st.params) × Cipher) =>
      D (simulate st.params c.1.1) c.1.2.1
        (@simTab (icPrg c.2) Hb CrtGen.tables st c.1.2.2.2 (simulate st.params c.1.1) c.1.1.1.2.1
          c.1.2.2.1) c.1.2.2.2 c.2)
    (fun E => @zk_post_h4_main_iub (icPrg E) Hb st w cs hm hzk hHb
      (fun o G3 G2 G5 => D o G3 G2 G5 E)
      (fun o G3 G2 G5 => Q5 o G3 G2 G5 E) (fun o G3 G2 G5 G5' => hQ5 o G3 G2 G5 G5' E)
      (fun c hc => hB (c, E) hc))
  refine (abs_sub_le _ _ _).trans ((add_le_add hA ((abs_sub_le _ _ _).trans
    (add_le_add hB4 hC))).trans (le_of_eq (by ring)))

set_option maxRecDepth 8000 in
/-- **`slot_zk_main`, identical until bad**: on the tape `USh × KS p` of `slot_zk_main`, if `D`
holds on the simulated side wherever the prediction holds, the advantage is at most
`εS q₃ q_E`. -/
theorem slot_zk_main_iub {cs : ByteArray → ByteArray → System GF128} (hm : MainP st.params)
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
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 E, (QE o G3 G2 G5 E).card ≤ qE)
    (hB : ∀ z : USh × KS st.params,
      mainPredIC Hb st hm Q5 (wPre w) ((z.2.1.2, (z.2.2.1, z.2.2.2, z.1.1)), z.1.2) →
      D (simulate st.params z.2.1.2) z.2.2.1
        (progRO st.params Hb st z.2.1.2 (shOf z.2.2.2 z.1)).1 z.1.1 z.1.2) :
    |pr (USh × KS st.params) (fun z =>
        D (realRO st.params Hb st w z.2.1.1 z.2.2.1 (shOf z.2.2.2 z.1)) z.2.2.1 z.2.2.2 z.1.1 z.1.2) -
      pr (USh × KS st.params) (fun z =>
        D (simulate st.params z.2.1.2) z.2.2.1
          (progRO st.params Hb st z.2.1.2 (shOf z.2.2.2 z.1)).1 z.1.1 z.1.2)| ≤ εS q3 qE := by
  have key := zk_rom_ic_h23_main_iub Hb st w hm hzk hHb hp D Q3 hQ3 hq3 Q5 hQ5 QE hQE hqE
    (fun c hc => hB ((c.1.2.2.2, c.2), ((Classical.arbitrary _, c.1.1), (c.1.2.1, c.1.2.2.1))) hc)
  have key' := key.trans (add_le_add (add_le_add le_rfl grindBad_le_113) le_rfl)
  let e1 : ((((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × Cipher) × SimCoins st.params) ≃
      USh × KS st.params :=
    { toFun := fun c => ((c.1.1.2.2, c.1.2), ((c.1.1.1.1, c.2), (c.1.1.2.1, c.1.1.1.2)))
      invFun := fun z => ((((z.2.1.1, z.2.2.2), (z.2.2.1, z.1.1)), z.1.2), z.2.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e2 : (((SimCoins st.params × Vis2 st.params) × Cipher) × Bytes 16) ≃ USh × KS st.params :=
    { toFun := fun c => ((c.1.1.2.2.2, c.1.2), ((c.2, c.1.1.1), (c.1.1.2.1, c.1.1.2.2.1)))
      invFun := fun z => (((z.2.1.2, (z.2.2.1, z.2.2.2, z.1.1)), z.1.2), z.2.1.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have r1 : pr (USh × KS st.params) (fun z =>
        D (realRO st.params Hb st w z.2.1.1 z.2.2.1 (shOf z.2.2.2 z.1)) z.2.2.1 z.2.2.2 z.1.1 z.1.2) =
      pr (((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × Cipher) (fun c =>
        D (@Prover.prove (icPrg c.2) (recH Hb st w c.1.2.1 c.1.1.2 c.1.2.2) CrtGen.tables st w
          (ba c.1.1.1) st.params.witnessBytes) c.1.2.1 c.1.1.2 c.1.2.2 c.2) := by
    rw [← pr_equiv e1]
    exact pr_prod_fst (β := SimCoins st.params)
      (fun c : ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × Cipher =>
        D (@Prover.prove (icPrg c.2) (recH Hb st w c.1.2.1 c.1.1.2 c.1.2.2) CrtGen.tables st w
          (ba c.1.1.1) st.params.witnessBytes) c.1.2.1 c.1.1.2 c.1.2.2 c.2)
  have r2 : pr (USh × KS st.params) (fun z =>
        D (simulate st.params z.2.1.2) z.2.2.1
          (progRO st.params Hb st z.2.1.2 (shOf z.2.2.2 z.1)).1 z.1.1 z.1.2) =
      pr ((SimCoins st.params × Vis2 st.params) × Cipher) (fun c =>
        D (simulate st.params c.1.1) c.1.2.1
          (@simTab (icPrg c.2) Hb CrtGen.tables st c.1.2.2.2 (simulate st.params c.1.1) c.1.1.1.2.1
            c.1.2.2.1) c.1.2.2.2 c.2) := by
    rw [← pr_equiv e2]
    exact pr_prod_fst (β := Bytes 16)
      (fun c : (SimCoins st.params × Vis2 st.params) × Cipher =>
        D (simulate st.params c.1.1) c.1.2.1
          (@simTab (icPrg c.2) Hb CrtGen.tables st c.1.2.2.2 (simulate st.params c.1.1) c.1.1.1.2.1
            c.1.2.2.1) c.1.2.2.2 c.2)
  rw [r1, r2]
  unfold εS
  exact key'

end Main

end VoleMole.ZK.Sim
