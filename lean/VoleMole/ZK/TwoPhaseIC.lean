import VoleMole.ZK.TwoPhaseRO
import VoleMole.ZK.GrindNum

/-!
# Two-phase zero knowledge in the random-oracle and ideal-cipher model with `H₂³` visible

The two-phase analogue of `zk_rom_ic_h23` (`ZK/HopsIC.lean`): the hybrids of `ZK/TwoPhaseRO.lean`
before H4 (`zk2_pre_h4`: H1, programming, the recomputed points and the uniform fallback block)
and after H4 (`zk2_post_h4`: the tape, H6, the simulator), each for every cipher table `E`, and H4
in the ideal-cipher model jointly over the root seed and `E` (`joint3_h4_2`, from
`hide_rom_query`), with the honest recomputation's reads counted: after H4 the two-phase view is a
function of the hidden part and `E`, and the run's public part (step 1's `chal1` and the key
columns, both through the reconstruction of the tape's opening) and the simulator's recomputation
of the grinding prefix read `E` only at the at most `4607` nodes `BAVC.reconstruct` rebuilds
(`hyb3'_ic_congr`, `hyb3'_ok_fields`, `viewIC2_congr`).

**`zk2_rom_ic_h23`.** For a base statement with dedicated label rows, a witness prefix `r` and a
continuation `k` whose instances and suffixes the witness satisfies (`Hyp2`), `HashesWF Hb` and
`SmallParams`, against a distinguisher that sees the two-phase output, `H₃`, `H₂³`, `H₅` and `E`
and reads `H₃`, `H₅`, `E` at `q₃`, `q₅`, `q_E` keys (`H₂³` freely), the real two-phase run (the
executable `voleGen` then `proveCommit`, with the ideal-cipher PRG `icPrg E`) and the simulated one
(`simRun2`, which reads `E` for `chal1` as the verifier does, with `H₂³` programmed by `simTab2`)
are at most

    q₃·2⁻¹²⁸ + Pr[GrindBad] + 221·(4607 + q_E + 4607)·2⁻¹²⁸ + (q₅ + 1)·2⁻¹²⁸

apart: the single-phase bound. The abort term `noHitProb` of `tapeHyp2_of_hops` is inside
`Pr[GrindBad]` (the fallback block is switched to a uniform one in the same hop as the programmed
points). **`zk2_rom_ic_h23_num`**: the same with `2⁻¹¹³` for `Pr[GrindBad]` (`grindBad_le_113`).
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

set_option linter.unusedSectionVars false

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy
  VoleMole.ZK.IC

/-! ## The chain around H4, for any PRG -/

section Generic

variable [HasPrg] (Hb : Hashes) (st : Statement) (r : ByteArray)

/-- **The two-phase hybrids before H4** (H1, grinding and programming, the programmed points
recomputed and the fallback block uniform), for any PRG. -/
theorem zk2_pre_h4 (kf : Tab5F → Cont2) (hHb : HashesWF Hb) (hh : ∀ G5, Hyp2 st r (kf G5))
    (D : Out2 → Tab3 → Tab2G st.params → Tab5F → Prop)
    (Q3 : Out2 → Tab3 → Tab2G st.params → Tab5F → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G2 G5, (∀ k ∈ Q3 o G3 G2 G5, G3 k = G3' k) →
      (D o G3 G2 G5 ↔ D o G3' G2 G5))
    {q3 : ℕ} (hq3 : ∀ o G3 G2 G5, (Q3 o G3 G2 G5).card ≤ q3) :
    |pr ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) (fun c =>
        D (realRun2 (recH Hb (st1 st) r c.2.1 c.1.2 c.2.2) CrtGen.tables st r (kf c.2.2) (ba c.1.1))
          c.2.1 c.1.2 c.2.2) -
      pr ((((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × Fallback st.params) ×
          (Tab3 × Tab5F)) (fun c =>
        Dp2 Hb CrtGen.tables st (kf c.2.2) D (hyb3' (recB Hb (st1 st) r c.2.1 c.2.2) CrtGen.tables st r (kf c.2.2)
          ((c.1.1.1.2, c.1.1.2.2), c.1.2)
          (hiddenOut st.params (ivOfPre Hb (st1 st) c.1.1.1.2) (ba (deltaOf c.1.1.2.2)) c.1.1.1.1))
          c.1.1.2.2 (c.2.1, c.1.1.2.1, c.2.2))| ≤
      q3 / 2 ^ 128 + pr Grind (GrindBad CrtGen.tables) := by
  have h1 := zk2_h1 Hb st r kf hHb hh D Q3 hQ3 hq3
  have h2 := zk2_prog Hb st r kf D
  have h3 := zk2_keys Hb st r kf hHb hh D
  have := abs_sub_le _ _ _ |>.trans (add_le_add h1 ((abs_sub_le _ _ _).trans (add_le_add h2 h3)))
  exact this.trans (le_of_eq (by ring))

/-- **The two-phase hybrids after H4** (the tape, H6, the simulator), for any PRG. -/
theorem zk2_post_h4 (kf : Tab5F → Cont2) (hHb : HashesWF Hb) (hh : ∀ G5, Hyp2 st r (kf G5))
    (QK5 : Tab5F → Finset (Bytes 37))
    (hQK5 : ∀ G5 G5', (∀ key ∈ QK5 G5, G5 key = G5' key) → kf G5 = kf G5')
    {qk5 : ℕ} (hqk5 : ∀ G5, (QK5 G5).card ≤ qk5)
    (D : Out2 → Tab3 → Tab2G st.params → Tab5F → Prop)
    (Q5 : Out2 → Tab3 → Tab2G st.params → Tab5F → Finset (Bytes 37))
    (hQ5 : ∀ o G3 G2 G5 G5', (∀ k ∈ Q5 o G3 G2 G5, G5 k = G5' k) →
      (D o G3 G2 G5 ↔ D o G3 G2 G5'))
    {q5 : ℕ} (hq5 : ∀ o G3 G2 G5, (Q5 o G3 G2 G5).card ≤ q5) :
    |pr ((Hidden st.params × ((Bytes 16 × Grind) × Fallback st.params)) × Vis2 st.params)
        (fun c => Dp2 Hb CrtGen.tables st (kf c.2.2.2) D (hyb3' (recB Hb (st1 st) r c.2.1 c.2.2.2)
          CrtGen.tables st r (kf c.2.2.2) c.1.2 (hiddenIdeal (ba (deltaOf c.1.2.1.2)) c.1.1)) c.1.2.1.2 c.2) -
      pr (SimCoins2 st.params × Vis2 st.params) (fun c =>
        Dp2 Hb CrtGen.tables st (kf c.2.2.2) D (simRun2 Hb st r.size (kf c.2.2.2) c.1) c.1.1.1.2.1 c.2)| ≤
      (q5 + qk5 + 1) / 2 ^ 128 := by
  have h5 := zk2_tape Hb st r kf D
  have h6 := zk2_h6 Hb st r kf hHb hh QK5 hQK5 hqk5 D Q5 hQ5 hq5
  have h7 := zk2_sim Hb st r kf hh D
  have := abs_sub_le _ _ _ |>.trans (add_le_add h5 ((abs_sub_le _ _ _).trans (add_le_add h6 h7)))
  exact this.trans (le_of_eq (by ring))

/-- **The final proof of the hybrid after H4**: if it is produced, its opening, `Δ` and `iv_pre`
are the tape's. -/
theorem hyb3'_ok_fields (k : Cont2) (Hs : Hashes) (T : CrtTables) (hh : Hyp2 st r k)
    (b : (Bytes 16 × Grind) × Fallback st.params) (o : Hidden st.params) {proof : ByteArray}
    (hok : (hyb3' Hs T st r k b o).2.2 = some (.ok proof)) :
    (⟨st.params, proof⟩ : Proof).opening = openingOf (ba (deltaOf b.1.2)) o.1 o.2.1 ∧
      (⟨st.params, proof⟩ : Proof).delta = ba (deltaOf b.1.2) ∧
      (⟨st.params, proof⟩ : Proof).ivPre = ba b.1.1 := by
  have e : hyb3' Hs T st r k b o = proveIdeal2 Hs T st r k (((b.1.1, b.1.2, o.1, o.2.1),
      withSib o.2.2 (sibOf Hs T (st1 st) (b.1.1, b.1.2, o.1, o.2.1)
        (withSib o.2.2 fun _ => fun _ => 0))), b.2) := rfl
  rw [e] at hok
  generalize withSib o.2.2 (sibOf Hs T (st1 st) (b.1.1, b.1.2, o.1, o.2.1)
    (withSib o.2.2 fun _ => fun _ => 0)) = t at hok
  rcases hf : firstHit b.1.2 with _ | ⟨ctr, δ⟩
  · simp only [proveIdeal2, hf, Option.map_eq_some_iff] at hok
    obtain ⟨_, _, he⟩ := hok
    cases he
  · simp only [proveIdeal2, hf, Option.map_eq_some_iff] at hok
    obtain ⟨⟨y, sfx⟩, hy, he⟩ := hok
    have hz := hh.hk _ _ _ hy
    rw [idealCore_fields Hs T (withInst st y) (r ++ sfx) y.sys hz.hvals hz.hdeg hz.hd hz.hd' hz.hI
      hz.hsat, Except.ok.injEq] at he
    subst he
    have hd : deltaOf b.1.2 = δ := by unfold deltaOf; rw [hf]; rfl
    have hacc := firstHit_accepts hf
    have hoc : openCount (ba δ) ≤ 105 := by
      unfold accepts at hacc; simp only [Bool.and_eq_true, decide_eq_true_eq] at hacc; exact hacc.2
    rw [hd]
    refine ⟨?_, ?_, ?_⟩
    · exact (fields_assemble st.params _).2.2.2.2.2.1.trans (fit_of_size (openingOf_size _ _ _ hoc))
    · exact (fields_assemble st.params _).2.2.2.2.2.2.1.trans (fit_of_size (size_ba _))
    · exact (fields_assemble st.params _).2.2.2.2.2.2.2.1.trans (fit_of_size (size_ba _))

end Generic

/-! ## The two-phase run reads the cipher only at the honest reads -/

section Congr

theorem idealPhase1_inst_congr (i1 i2 : HasPrg) (Hs : Hashes) (T : CrtTables) (st : Statement)
    (r : ByteArray) (s : Shared) (ctr : ℕ) (δ : Bytes 16) (t : Pads st.params)
    (hP : @pubOf i1 Hs st s δ = @pubOf i2 Hs st s δ)
    (hQ : ∀ c, @qcolsOf i1 st (@pubOf i2 Hs st s δ) δ c = @qcolsOf i2 st (@pubOf i2 Hs st s δ) δ c) :
    @idealPhase1 i1 Hs T st r s ctr δ t = @idealPhase1 i2 Hs T st r s ctr δ t := by
  simp only [idealPhase1, cmultIdeal, tUt, tC1, tF1, tF0, hP, hQ]

theorem proveIdeal2_inst_congr (i1 i2 : HasPrg) (Hs : Hashes) (T : CrtTables) (st : Statement)
    (r : ByteArray) (k : Cont2) (t : IdealTape2 st.params)
    (hP : @pubOf i1 Hs (st1 st) t.1.1 (deltaOf t.1.1.2.1) =
      @pubOf i2 Hs (st1 st) t.1.1 (deltaOf t.1.1.2.1))
    (hQ : ∀ c, @qcolsOf i1 (st1 st) (@pubOf i2 Hs (st1 st) t.1.1 (deltaOf t.1.1.2.1))
        (deltaOf t.1.1.2.1) c =
      @qcolsOf i2 (st1 st) (@pubOf i2 Hs (st1 st) t.1.1 (deltaOf t.1.1.2.1)) (deltaOf t.1.1.2.1) c) :
    @proveIdeal2 i1 Hs T st r k t = @proveIdeal2 i2 Hs T st r k t := by
  unfold proveIdeal2
  rcases hf : firstHit t.1.1.2.1 with _ | ⟨ctr, δ⟩
  · rfl
  · have hd : deltaOf t.1.1.2.1 = δ := by unfold deltaOf; rw [hf]; rfl
    rw [hd] at hP hQ
    dsimp only
    rw [idealPhase1_inst_congr i1 i2 Hs T (st1 st) r t.1.1 ctr δ t.1.2 hP hQ]
    refine congrArg _ (congrArg _ (map_congr_of fun z _ => ?_))
    exact idealCore_inst_congr i1 i2 Hs T (withInst st z.1) (r ++ z.2) t.1.1 ctr δ t.1.2 hP hQ

variable {E E' : Cipher}

/-- **The two-phase hybrid after H4 reads the cipher only at the honest reads of its tape.** -/
theorem hyb3'_ic_congr (Hs : Hashes) (T : CrtTables) (st : Statement) (r : ByteArray) (k : Cont2)
    (b : (Bytes 16 × Grind) × Fallback st.params) (o : Hidden st.params)
    (h : ∀ key ∈ hRd E Hs (st1 st) (b.1.1, b.1.2, o.1, o.2.1) (deltaOf b.1.2), E key = E' key) :
    @hyb3' (icPrg E) Hs T st r k b o = @hyb3' (icPrg E') Hs T st r k b o := by
  have hP := pubOf_ic_congr Hs (st1 st) (b.1.1, b.1.2, o.1, o.2.1) (deltaOf b.1.2) h
  have hQ := fun c => (qcolsOf_ic_congr Hs (st1 st) (b.1.1, b.1.2, o.1, o.2.1) (deltaOf b.1.2) h c).symm
  unfold hyb3' fillSib tapeOfHidden
  dsimp only
  rewrite [sibOf_inst_congr (icPrg E) (icPrg E') Hs T (st1 st) _ _ hP hQ]
  exact proveIdeal2_inst_congr (icPrg E) (icPrg E') Hs T st r k _ hP hQ

end Congr

/-! ## H4 in the ideal-cipher model, two phases -/

section IC

variable (Hb : Hashes) (st : Statement) (r : ByteArray) (K : Tab5F → Cipher → Cont2)

/-- **The distinguisher's view after the programmed points are recomputed** (two phases), as a
function of the hidden part `o` and the cipher table `E`; the continuation `K G5 E` may read the
`H₅` table and the cipher. -/
noncomputable def viewIC2 (D : Out2 → Tab3 → Tab2G st.params → Tab5F → Cipher → Prop)
    (a : Bytes 16) (g : Grind) (fb : Fallback st.params) (v : Vis2 st.params) (o : Hidden st.params)
    (E : Cipher) : Prop :=
  @Dp2 (icPrg E) Hb CrtGen.tables st (K v.2.2 E) (fun o G3 G2 G5 => D o G3 G2 G5 E)
    (@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r (K v.2.2 E) ((a, g), fb) o)
    g v

/-- **The keys the two-phase view reads**: the distinguisher's, the honest recomputation's and
the continuation's. -/
noncomputable def viewKeys2 (QE : Out2 → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset Blk)
    (QKE : Tab5F → Cipher → Finset Blk)
    (a : Bytes 16) (g : Grind) (fb : Fallback st.params) (v : Vis2 st.params) (o : Hidden st.params)
    (E : Cipher) : Finset Blk :=
  QE (@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r (K v.2.2 E) ((a, g), fb) o)
      v.1 (@simTab2 (icPrg E) Hb CrtGen.tables st (K v.2.2 E) v.2.2
        (@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r (K v.2.2 E) ((a, g), fb)
          o) g v.2.1) v.2.2 E ∪
    hRd E (recB Hb (st1 st) r v.1 v.2.2) (st1 st) (a, g, o.1, o.2.1) (deltaOf g) ∪ QKE v.2.2 E

variable {Hb st r K}

/-- **The two-phase view reads the cipher only at `viewKeys2`.** -/
theorem viewIC2_congr (hh : ∀ G5 E, Hyp2 st r (K G5 E))
    (QKE : Tab5F → Cipher → Finset Blk)
    (hQKE : ∀ G5 E E', (∀ key ∈ QKE G5 E, E key = E' key) → K G5 E = K G5 E')
    (D : Out2 → Tab3 → Tab2G st.params → Tab5F → Cipher → Prop)
    (QE : Out2 → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset Blk)
    (hQE : ∀ o G3 G2 G5 E E', (∀ k ∈ QE o G3 G2 G5 E, E k = E' k) →
      (D o G3 G2 G5 E ↔ D o G3 G2 G5 E'))
    (a : Bytes 16) (g : Grind) (fb : Fallback st.params) (v : Vis2 st.params) (o : Hidden st.params)
    (E E' : Cipher) (hE : ∀ key ∈ viewKeys2 Hb st r K QE QKE a g fb v o E, E key = E' key) :
    viewIC2 Hb st r K D a g fb v o E ↔ viewIC2 Hb st r K D a g fb v o E' := by
  obtain ⟨G3, G2, G5⟩ := v
  set R := recB Hb (st1 st) r G3 G5 with hR
  have hK : K G5 E' = K G5 E := (hQKE G5 E E' fun key hk =>
    hE key (Finset.mem_union_right _ hk)).symm
  have hrd : ∀ key ∈ hRd E R (st1 st) (a, g, o.1, o.2.1) (deltaOf g), E key = E' key :=
    fun key hk => hE key (Finset.mem_union_left _ (Finset.mem_union_right _ hk))
  have hout : @hyb3' (icPrg E) R CrtGen.tables st r (K G5 E) ((a, g), fb) o =
      @hyb3' (icPrg E') R CrtGen.tables st r (K G5 E) ((a, g), fb) o :=
    hyb3'_ic_congr R CrtGen.tables st r (K G5 E) ((a, g), fb) o hrd
  have htab : @simTab2 (icPrg E) Hb CrtGen.tables st (K G5 E) G5
      (@hyb3' (icPrg E) R CrtGen.tables st r (K G5 E) ((a, g), fb) o) g G2 =
      @simTab2 (icPrg E') Hb CrtGen.tables st (K G5 E) G5
        (@hyb3' (icPrg E) R CrtGen.tables st r (K G5 E) ((a, g), fb) o) g G2 := by
    unfold simTab2 outPre2
    rcases ho : (@hyb3' (icPrg E) R CrtGen.tables st r (K G5 E) ((a, g), fb) o).2.2 with
      _ | e | proof
    · rfl
    · rfl
    rcases hk1 : K G5 E ((@hyb3' (icPrg E) R CrtGen.tables st r (K G5 E) ((a, g), fb) o).1,
      (@hyb3' (icPrg E) R CrtGen.tables st r (K G5 E) ((a, g), fb) o).2.1) with _ | ⟨y, sfx⟩
    · rfl
    obtain ⟨hO, hD, hI⟩ := @hyb3'_ok_fields (icPrg E) st r (K G5 E) R CrtGen.tables (hh G5 E)
      ((a, g), fb) o proof ho
    have hv : @vPre (icPrg E) (rec5 Hb G5) CrtGen.tables (withInst st y) proof =
        @vPre (icPrg E') (rec5 Hb G5) CrtGen.tables (withInst st y) proof := by
      refine vPre_ic_congr (rec5 Hb G5) CrtGen.tables (withInst st y) proof fun key hk => hrd key ?_
      rw [ivOf, hO, hD, hI, rec5_h4, rec5_mu1] at hk
      rw [hRd, hR, recB, recH_hash_ne (by decide) (by decide) (by decide), recH_mu1]
      exact hk
    simp only [hv]
  show D (@hyb3' (icPrg E) R CrtGen.tables st r (K G5 E) ((a, g), fb) o) G3
      (@simTab2 (icPrg E) Hb CrtGen.tables st (K G5 E) G5
        (@hyb3' (icPrg E) R CrtGen.tables st r (K G5 E) ((a, g), fb) o) g G2) G5 E ↔
    D (@hyb3' (icPrg E') R CrtGen.tables st r (K G5 E') ((a, g), fb) o) G3
      (@simTab2 (icPrg E') Hb CrtGen.tables st (K G5 E') G5
        (@hyb3' (icPrg E') R CrtGen.tables st r (K G5 E') ((a, g), fb) o) g G2) G5 E'
  rw [hK, ← hout, ← htab]
  exact hQE _ _ _ _ _ _ fun key hk =>
    hE key (Finset.mem_union_left _ (Finset.mem_union_left _ hk))

theorem viewKeys2_card
    (QE : Out2 → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset Blk)
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 E, (QE o G3 G2 G5 E).card ≤ qE)
    (QKE : Tab5F → Cipher → Finset Blk) {qkE : ℕ} (hqkE : ∀ G5 E, (QKE G5 E).card ≤ qkE)
    (a : Bytes 16) (g : Grind) (fb : Fallback st.params) (v : Vis2 st.params) (o : Hidden st.params)
    (E : Cipher) :
    (viewKeys2 Hb st r K QE QKE a g fb v o E).card ≤ (qE + qkE) + 4607 := by
  unfold viewKeys2
  have h1 := card_union_le (QE (@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r
      (K v.2.2 E) ((a, g), fb) o) v.1 (@simTab2 (icPrg E) Hb CrtGen.tables st (K v.2.2 E) v.2.2
        (@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r (K v.2.2 E) ((a, g), fb)
          o) g v.2.1) v.2.2 E)
    (hRd E (recB Hb (st1 st) r v.1 v.2.2) (st1 st) (a, g, o.1, o.2.1) (deltaOf g))
  have h2 := card_union_le (QE (@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r
      (K v.2.2 E) ((a, g), fb) o) v.1 (@simTab2 (icPrg E) Hb CrtGen.tables st (K v.2.2 E) v.2.2
        (@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r (K v.2.2 E) ((a, g), fb)
          o) g v.2.1) v.2.2 E ∪
    hRd E (recB Hb (st1 st) r v.1 v.2.2) (st1 st) (a, g, o.1, o.2.1) (deltaOf g)) (QKE v.2.2 E)
  have h3 := hqE (@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r
      (K v.2.2 E) ((a, g), fb) o) v.1 (@simTab2 (icPrg E) Hb CrtGen.tables st (K v.2.2 E) v.2.2
        (@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r (K v.2.2 E) ((a, g), fb)
          o) g v.2.1) v.2.2 E
  have h4 : (hRd E (recB Hb (st1 st) r v.1 v.2.2) (st1 st) (a, g, o.1, o.2.1) (deltaOf g)).card ≤
      4607 := rdKeys_card _ _ _ _
  have h5 := hqkE v.2.2 E
  omega

variable (Hb st r K)

/-- **H4 in the ideal-cipher model, two phases**: the hidden part computed with `E` from a uniform
root seed against the ideal hidden part, `E` uniform and read by the distinguisher at `q_E` keys,
by the continuation at `q_kE` keys and by the honest recomputation at `≤ 4607` keys. -/
theorem joint3_h4_2 (hp : SmallParams st.params) (hh : ∀ G5 E, Hyp2 st r (K G5 E))
    (QKE : Tab5F → Cipher → Finset Blk)
    (hQKE : ∀ G5 E E', (∀ key ∈ QKE G5 E, E key = E' key) → K G5 E = K G5 E')
    {qkE : ℕ} (hqkE : ∀ G5 E, (QKE G5 E).card ≤ qkE)
    (D : Out2 → Tab3 → Tab2G st.params → Tab5F → Cipher → Prop)
    (QE : Out2 → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset Blk)
    (hQE : ∀ o G3 G2 G5 E E', (∀ k ∈ QE o G3 G2 G5 E, E k = E' k) →
      (D o G3 G2 G5 E ↔ D o G3 G2 G5 E'))
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 E, (QE o G3 G2 G5 E).card ≤ qE) :
    |pr (((((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × Fallback st.params) ×
          (Tab3 × Tab5F)) × Cipher)
        (fun c => @Dp2 (icPrg c.2) Hb CrtGen.tables st (K c.1.2.2 c.2)
          (fun o G3 G2 G5 => D o G3 G2 G5 c.2)
          (@hyb3' (icPrg c.2) (recB Hb (st1 st) r c.1.2.1 c.1.2.2) CrtGen.tables st r
            (K c.1.2.2 c.2) ((c.1.1.1.1.2, c.1.1.1.2.2), c.1.1.2)
            (@hiddenOut (icPrg c.2) st.params (ivOfPre Hb (st1 st) c.1.1.1.1.2)
              (ba (deltaOf c.1.1.1.2.2)) c.1.1.1.1.1))
          c.1.1.1.2.2 (c.1.2.1, c.1.1.1.2.1, c.1.2.2)) -
      pr (((Hidden st.params × ((Bytes 16 × Grind) × Fallback st.params)) × Vis2 st.params) ×
          Cipher) (fun c =>
        @Dp2 (icPrg c.2) Hb CrtGen.tables st (K c.1.2.2.2 c.2) (fun o G3 G2 G5 => D o G3 G2 G5 c.2)
          (@hyb3' (icPrg c.2) (recB Hb (st1 st) r c.1.2.1 c.1.2.2.2) CrtGen.tables st r
            (K c.1.2.2.2 c.2) c.1.1.2 (hiddenIdeal (ba (deltaOf c.1.1.2.1.2)) c.1.1.1)) c.1.1.2.1.2
          c.1.2)| ≤
      221 * (4607 + ((qE + qkE : ℕ) + 4607)) / 2 ^ 128 := by
  let E2 : (((Bytes 16 × Grind) × Fallback st.params) × Vis2 st.params) × (Blk × Cipher) ≃
      ((((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × Fallback st.params) ×
        (Tab3 × Tab5F)) × Cipher :=
    { toFun := fun c => (((((c.2.1, c.1.1.1.1), (c.1.2.2.1, c.1.1.1.2)), c.1.1.2),
        (c.1.2.1, c.1.2.2.2)), c.2.2)
      invFun := fun c => ((((c.1.1.1.1.2, c.1.1.1.2.2), c.1.1.2), (c.1.2.1, c.1.1.1.2.1, c.1.2.2)),
        (c.1.1.1.1.1, c.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let E3 : (((Bytes 16 × Grind) × Fallback st.params) × Vis2 st.params) × (Hidden st.params × Cipher) ≃
      ((Hidden st.params × ((Bytes 16 × Grind) × Fallback st.params)) × Vis2 st.params) × Cipher :=
    { toFun := fun c => (((c.2.1, c.1.1), c.1.2), c.2.2)
      invFun := fun c => ((c.1.1.2, c.1.2), (c.1.1.1, c.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv E2, ← pr_equiv E3]
  refine abs_pr_prod_sub_le _ _ fun x => ?_
  obtain ⟨⟨⟨a, g⟩, fb⟩, v⟩ := x
  have h := hide_rom_query st.params (ivOfPre Hb (st1 st) a) (ba (deltaOf g)) hp
    (viewIC2 Hb st r K D a g fb v) (viewKeys2 Hb st r K QE QKE a g fb v)
    (fun o E E' hk => viewIC2_congr hh QKE hQKE D QE hQE a g fb v o E E' hk)
    (viewKeys2_card QE hqE QKE hqkE a g fb v)
  unfold IC.realPr IC.idealPr at h
  have e : pr (Blk × Cipher) (fun p => viewIC2 Hb st r K D a g fb v
        (hiddenOutE p.2 st.params (ivOfPre Hb (st1 st) a) (ba (deltaOf g)) p.1) p.2) =
      pr (Blk × Cipher) (fun p => viewIC2 Hb st r K D a g fb v
        (@hiddenOut (icPrg p.2) st.params (ivOfPre Hb (st1 st) a) (ba (deltaOf g)) p.1) p.2) :=
    pr_congr fun p => by rw [hiddenOut_ic]
  rw [e] at h
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

end IC

/-! ## The end-to-end statement -/

section Main

variable (Hb : Hashes) (st : Statement) (r : ByteArray) (K : Tab5F → Cipher → Cont2)

/-- **Two-phase zero knowledge in the random-oracle and ideal-cipher model with `H₂³` visible**
(label-row layout, faest-arch-opt's tables; PomFRIT's flow: step 1 with the witness prefix `r`,
the continuation picks the instance and the witness suffix from step 1's output, step 2).

The hash record is `recH Hb (st1 st) r G3 G2 G5` (`H₃` a uniform table at step 1's seed inputs,
`H₂³` at every grinding point, `H₅` at every 37-byte input) and the cipher a uniform table `E`; the
real world is the **executable two-phase run** `realRun2` (`Prover.voleGen` then
`Prover.proveCommit`) with the ideal-cipher PRG `icPrg E`. **The continuation `K G5 E` may depend
on the `H₅` table and the cipher** (not on `H₃` or `H₂³`), reading them at `q_k5`, `q_kE` keys
(`QK5`, `QKE`): in a game it is the rest of the game up to this proof's instance, which may run
other proofs on the same tables. The simulator outputs `simRun2 Hb` (its coins only, and `E` for
the verifier's `chal1`) and the `H₂³` table `simTab2`: `G2` programmed at the grinding points of
the prefix it recomputes from its final proof for the instance the continuation picks from its
step-1 output.

Against a distinguisher that sees the output, the three tables and `E`, reads `H₃`, `H₅`, `E` at
`q₃`, `q₅`, `q_E` keys and `H₂³` freely, the advantage is at most

    q₃·2⁻¹²⁸ + Pr[GrindBad] + 221·(4607 + (q_E + q_kE) + 4607)·2⁻¹²⁸ + ((q₅ + q_k5) + 1)·2⁻¹²⁸

(the continuation's reads count as the distinguisher's: they are made before the instance is
fixed, so the H4 and H6 hops must hide them too). -/
theorem zk2_rom_ic_h23 (hh : ∀ G5 E, Hyp2 st r (K G5 E)) (hHb : HashesWF Hb)
    (hp : SmallParams st.params)
    (QK5 : Tab5F → Cipher → Finset (Bytes 37))
    (hQK5 : ∀ G5 G5' E, (∀ key ∈ QK5 G5 E, G5 key = G5' key) → K G5 E = K G5' E)
    {qk5 : ℕ} (hqk5 : ∀ G5 E, (QK5 G5 E).card ≤ qk5)
    (QKE : Tab5F → Cipher → Finset Blk)
    (hQKE : ∀ G5 E E', (∀ key ∈ QKE G5 E, E key = E' key) → K G5 E = K G5 E')
    {qkE : ℕ} (hqkE : ∀ G5 E, (QKE G5 E).card ≤ qkE)
    (D : Out2 → Tab3 → Tab2G st.params → Tab5F → Cipher → Prop)
    (Q3 : Out2 → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G2 G5 E, (∀ k ∈ Q3 o G3 G2 G5 E, G3 k = G3' k) →
      (D o G3 G2 G5 E ↔ D o G3' G2 G5 E))
    {q3 : ℕ} (hq3 : ∀ o G3 G2 G5 E, (Q3 o G3 G2 G5 E).card ≤ q3)
    (Q5 : Out2 → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset (Bytes 37))
    (hQ5 : ∀ o G3 G2 G5 G5' E, (∀ k ∈ Q5 o G3 G2 G5 E, G5 k = G5' k) →
      (D o G3 G2 G5 E ↔ D o G3 G2 G5' E))
    {q5 : ℕ} (hq5 : ∀ o G3 G2 G5 E, (Q5 o G3 G2 G5 E).card ≤ q5)
    (QE : Out2 → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset Blk)
    (hQE : ∀ o G3 G2 G5 E E', (∀ k ∈ QE o G3 G2 G5 E, E k = E' k) →
      (D o G3 G2 G5 E ↔ D o G3 G2 G5 E'))
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 E, (QE o G3 G2 G5 E).card ≤ qE) :
    |pr (((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × Cipher) (fun c =>
        D (@realRun2 (icPrg c.2) (recH Hb (st1 st) r c.1.2.1 c.1.1.2 c.1.2.2) CrtGen.tables st r
          (K c.1.2.2 c.2) (ba c.1.1.1)) c.1.2.1 c.1.1.2 c.1.2.2 c.2) -
      pr ((SimCoins2 st.params × Vis2 st.params) × Cipher) (fun c =>
        D (@simRun2 (icPrg c.2) Hb st r.size (K c.1.2.2.2 c.2) c.1.1) c.1.2.1
          (@simTab2 (icPrg c.2) Hb CrtGen.tables st (K c.1.2.2.2 c.2) c.1.2.2.2
            (@simRun2 (icPrg c.2) Hb st r.size (K c.1.2.2.2 c.2) c.1.1) c.1.1.1.1.2.1 c.1.2.2.1)
          c.1.2.2.2 c.2)| ≤
      q3 / 2 ^ 128 + pr Grind (GrindBad CrtGen.tables) +
        221 * (4607 + ((qE + qkE : ℕ) + 4607)) / 2 ^ 128 + ((q5 + qk5 : ℕ) + 1) / 2 ^ 128 := by
  have hA := abs_pr_avgE
    (fun (c : (Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) (E : Cipher) =>
      D (@realRun2 (icPrg E) (recH Hb (st1 st) r c.2.1 c.1.2 c.2.2) CrtGen.tables st r (K c.2.2 E)
        (ba c.1.1)) c.2.1 c.1.2 c.2.2 E)
    (fun (c : (((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × Fallback st.params) ×
        (Tab3 × Tab5F)) (E : Cipher) =>
      @Dp2 (icPrg E) Hb CrtGen.tables st (K c.2.2 E) (fun o G3 G2 G5 => D o G3 G2 G5 E)
        (@hyb3' (icPrg E) (recB Hb (st1 st) r c.2.1 c.2.2) CrtGen.tables st r (K c.2.2 E)
          ((c.1.1.1.2, c.1.1.2.2), c.1.2)
          (@hiddenOut (icPrg E) st.params (ivOfPre Hb (st1 st) c.1.1.1.2) (ba (deltaOf c.1.1.2.2))
            c.1.1.1.1))
        c.1.1.2.2 (c.2.1, c.1.1.2.1, c.2.2))
    (fun E => @zk2_pre_h4 (icPrg E) Hb st r (fun G5 => K G5 E) hHb (fun G5 => hh G5 E)
      (fun o G3 G2 G5 => D o G3 G2 G5 E)
      (fun o G3 G2 G5 => Q3 o G3 G2 G5 E) (fun o G3 G3' G2 G5 => hQ3 o G3 G3' G2 G5 E) q3
      (fun o G3 G2 G5 => hq3 o G3 G2 G5 E))
  have hB := joint3_h4_2 Hb st r K hp hh QKE hQKE hqkE D QE hQE hqE
  have hC := abs_pr_avgE
    (fun (c : (Hidden st.params × ((Bytes 16 × Grind) × Fallback st.params)) × Vis2 st.params)
        (E : Cipher) =>
      @Dp2 (icPrg E) Hb CrtGen.tables st (K c.2.2.2 E) (fun o G3 G2 G5 => D o G3 G2 G5 E)
        (@hyb3' (icPrg E) (recB Hb (st1 st) r c.2.1 c.2.2.2) CrtGen.tables st r (K c.2.2.2 E) c.1.2
          (hiddenIdeal (ba (deltaOf c.1.2.1.2)) c.1.1)) c.1.2.1.2 c.2)
    (fun (c : SimCoins2 st.params × Vis2 st.params) (E : Cipher) =>
      D (@simRun2 (icPrg E) Hb st r.size (K c.2.2.2 E) c.1) c.2.1
        (@simTab2 (icPrg E) Hb CrtGen.tables st (K c.2.2.2 E) c.2.2.2
          (@simRun2 (icPrg E) Hb st r.size (K c.2.2.2 E) c.1) c.1.1.1.2.1 c.2.2.1) c.2.2.2 E)
    (fun E => @zk2_post_h4 (icPrg E) Hb st r (fun G5 => K G5 E) hHb (fun G5 => hh G5 E)
      (fun G5 => QK5 G5 E) (fun G5 G5' => hQK5 G5 G5' E) qk5 (fun G5 => hqk5 G5 E)
      (fun o G3 G2 G5 => D o G3 G2 G5 E)
      (fun o G3 G2 G5 => Q5 o G3 G2 G5 E) (fun o G3 G2 G5 G5' => hQ5 o G3 G2 G5 G5' E) q5
      (fun o G3 G2 G5 => hq5 o G3 G2 G5 E))
  refine (abs_sub_le _ _ _).trans ((add_le_add hA ((abs_sub_le _ _ _).trans
    (add_le_add hB hC))).trans (le_of_eq (by push_cast; ring)))

/-- **`zk2_rom_ic_h23` with `Pr[GrindBad] ≤ 2⁻¹¹³`**: the two-phase prover's zero-knowledge error
in the ROM and ideal-cipher model is the single-phase one (`εRO`, `ZK/ReadsRO.lean`) at the
distinguisher's budget plus the continuation's reads:
`q₃·2⁻¹²⁸ + 2⁻¹¹³ + 221·(4607 + (q_E + q_kE) + 4607)·2⁻¹²⁸ + ((q₅ + q_k5) + 1)·2⁻¹²⁸`. -/
theorem zk2_rom_ic_h23_num (hh : ∀ G5 E, Hyp2 st r (K G5 E)) (hHb : HashesWF Hb)
    (hp : SmallParams st.params)
    (QK5 : Tab5F → Cipher → Finset (Bytes 37))
    (hQK5 : ∀ G5 G5' E, (∀ key ∈ QK5 G5 E, G5 key = G5' key) → K G5 E = K G5' E)
    {qk5 : ℕ} (hqk5 : ∀ G5 E, (QK5 G5 E).card ≤ qk5)
    (QKE : Tab5F → Cipher → Finset Blk)
    (hQKE : ∀ G5 E E', (∀ key ∈ QKE G5 E, E key = E' key) → K G5 E = K G5 E')
    {qkE : ℕ} (hqkE : ∀ G5 E, (QKE G5 E).card ≤ qkE)
    (D : Out2 → Tab3 → Tab2G st.params → Tab5F → Cipher → Prop)
    (Q3 : Out2 → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G2 G5 E, (∀ k ∈ Q3 o G3 G2 G5 E, G3 k = G3' k) →
      (D o G3 G2 G5 E ↔ D o G3' G2 G5 E))
    {q3 : ℕ} (hq3 : ∀ o G3 G2 G5 E, (Q3 o G3 G2 G5 E).card ≤ q3)
    (Q5 : Out2 → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset (Bytes 37))
    (hQ5 : ∀ o G3 G2 G5 G5' E, (∀ k ∈ Q5 o G3 G2 G5 E, G5 k = G5' k) →
      (D o G3 G2 G5 E ↔ D o G3 G2 G5' E))
    {q5 : ℕ} (hq5 : ∀ o G3 G2 G5 E, (Q5 o G3 G2 G5 E).card ≤ q5)
    (QE : Out2 → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset Blk)
    (hQE : ∀ o G3 G2 G5 E E', (∀ k ∈ QE o G3 G2 G5 E, E k = E' k) →
      (D o G3 G2 G5 E ↔ D o G3 G2 G5 E'))
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 E, (QE o G3 G2 G5 E).card ≤ qE) :
    |pr (((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × Cipher) (fun c =>
        D (@realRun2 (icPrg c.2) (recH Hb (st1 st) r c.1.2.1 c.1.1.2 c.1.2.2) CrtGen.tables st r
          (K c.1.2.2 c.2) (ba c.1.1.1)) c.1.2.1 c.1.1.2 c.1.2.2 c.2) -
      pr ((SimCoins2 st.params × Vis2 st.params) × Cipher) (fun c =>
        D (@simRun2 (icPrg c.2) Hb st r.size (K c.1.2.2.2 c.2) c.1.1) c.1.2.1
          (@simTab2 (icPrg c.2) Hb CrtGen.tables st (K c.1.2.2.2 c.2) c.1.2.2.2
            (@simRun2 (icPrg c.2) Hb st r.size (K c.1.2.2.2 c.2) c.1.1) c.1.1.1.1.2.1 c.1.2.2.1)
          c.1.2.2.2 c.2)| ≤
      q3 / 2 ^ 128 + 1 / 2 ^ 113 + 221 * (4607 + ((qE + qkE : ℕ) + 4607)) / 2 ^ 128 +
        ((q5 + qk5 : ℕ) + 1) / 2 ^ 128 :=
  (zk2_rom_ic_h23 Hb st r K hh hHb hp QK5 hQK5 hqk5 QKE hQKE hqkE D Q3 hQ3 hq3 Q5 hQ5 hq5 QE hQE
    hqE).trans (add_le_add (add_le_add (add_le_add le_rfl grindBad_le_113) le_rfl) le_rfl)

end Main

end VoleMole.ZK.Sim
