import VoleMole.ZK.MainSharedKeys
import VoleMole.ZK.MainGame

/-!
# One `main`-layout proof among others on a shared `H₅` table and cipher (`lean/docs/zk.md` §4.2)

The joint hop of `ZK/MainGame.lean` gives each proof its own tables. Here the proofs of a game
**share** the `H₅` table (on every 37-byte input) and the cipher table; each proof keeps its own
`H₃` slice and its own `H₂³` table (`VP p`), both visible to the adversary, the second programmed
by the simulator (`progRO`).

* `USh = Tab5F × Cipher`: the shared tables. `VP p = Tab3 × Tab2G p`: a proof's own tables.
* `realRO_congr5`, `realRO_congrE`, `progRO_congr5`, `progRO_congrE`: the executable prover
  (`realRO`) reads `H₅` only at `realKeys5` and the cipher only at `realKeysE`; the simulator's
  programming reads them only at `progKeys5`, `progKeysE` (the statements behind `realRO_rd5`,
  `realRO_rdE`, `progRO_isProg`, with the key sets explicit).
* **`slot_zk_main`**: `zk_rom_ic_h23_main_num` on one tape `USh × ((ρ, simulator coins) × VP p)`
  for both experiments (the real one ignores the simulator's coins, the simulated one `ρ`), so
  that a game can switch one proof from real to simulated on a fixed tape:

      |Pr[D(real)] − Pr[D(sim)]| ≤ εS q₃ q_E + Pr[w[0..16) ∈ candIC]

  with `εS q₃ q_E = q₃·2⁻¹²⁸ + 2⁻¹¹³ + 221·(4607 + q_E + 4607)·2⁻¹²⁸` and the candidate set that
  of the distinguisher's explicit `H₅` read set `Q5` on the simulated proof.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy
  VoleMole.ZK.IC

attribute [local instance] decEqW128

/-- **The tables the proofs of a game share**: `H₅` on every 37-byte input, and the cipher. -/
abbrev USh := Tab5F × Cipher

/-- **A proof's own tables**: its `H₃` slice and its `H₂³` table. -/
abbrev VP (p : Params) := Tab3 × Tab2G p

/-- The tables of one proof: its own `H₂³` table with the shared `H₅` table and cipher. -/
abbrev shOf {p : Params} (G2 : Tab2G p) (u : USh) : Sh p := (G2, u.1, u.2)

/-! ## What the prover and the programming read, with the key sets explicit -/

section Reads

variable (p : Params) (Hb : Hashes) (st : Statement) (w : ByteArray)

/-- **The real prover reads `H₅` only at `realKeys5`.** -/
theorem realRO_congr5 (ρ : Bytes 16) (G3 : Tab3) (s : Sh p) (G5 : Tab5F)
    (h : ∀ k ∈ realKeys5 p Hb st w (ba ρ) G3 s, s.2.1 k = G5 k) :
    realRO p Hb st w ρ G3 (s.1, G5, s.2.2) = realRO p Hb st w ρ G3 s := by
  classical
  have hA := recHp_agreeOff_h5 (Hb := Hb) (st := st) (w := w) G3 s.1 G5 s.2.1
  unfold realRO realROb Prover.prove
  dsimp only
  rw [@voleGen_eq_voleGenAt (icPrg (rowFn s.2.2)), @voleGen_eq_voleGenAt (icPrg (rowFn s.2.2)),
    proveCommit_agreeOff_h5 hA, recHp_mu1, recHp_mu1, recHp_h3, recHp_h3]
  refine congrArg _ (@voleGenAt_h5_congr (icPrg (rowFn s.2.2)) _ _ hA _ _ _ _ _ _ _ fun x hx => ?_)
  rw [@vgIn5_agreeOff (icPrg (rowFn s.2.2)) _ _ hA] at hx
  refine withTable_h5_congr _ fun hs => (h _ (mem_image.2 ⟨x, ?_, rfl⟩)).symm
  rw [List.mem_toFinset]
  simpa only [realKeys5, rSeed, recHp_mu1, recHp_h3] using hx

/-- **The real prover reads the cipher only at `realKeysE`.** -/
theorem realRO_congrE (hHb : HashesWF Hb) (ρ : Bytes 16) (G3 : Tab3) (s : Sh p) (E : Cipher)
    (h : ∀ k ∈ realKeysE p Hb st w (ba ρ) G3 s, s.2.2 k = E k) :
    realRO p Hb st w ρ G3 (s.1, s.2.1, E) = realRO p Hb st w ρ G3 s := by
  have hs : (rSeed (recHp p Hb st w G3 s.1 s.2.1) st w (ba ρ)).size = 16 := by
    rw [rSeed, ByteArray.size_extract, recHp_wf hHb]; rfl
  unfold realRO realROb Prover.prove
  dsimp only
  rw [@voleGen_eq_voleGenAt (icPrg (rowFn E)), @voleGen_eq_voleGenAt (icPrg (rowFn s.2.2))]
  refine congrArg _ (voleGenAt_ic_congr _ _ _ _ _ _ _ hs fun n hn _ => ?_).symm
  exact rowFn_congr (h _ (mem_image.2 ⟨n, mem_range.2 hn, rfl⟩))

lemma card_realKeysE (ρ : ByteArray) (G3 : Tab3) (s : Sh p) :
    (realKeysE p Hb st w ρ G3 s).card ≤ 4607 :=
  card_image_le.trans (le_of_eq (by rw [card_range]; rfl))

variable {p}

/-- **The programming reads `H₅` only at `progKeys5`.** -/
theorem progRO_congr5 (c : SimCoins p) (s : Sh p) (G5 : Tab5F)
    (h : ∀ k ∈ progKeys5 Hb st (simulate p c) s, s.2.1 k = G5 k) :
    (progRO p Hb st c (s.1, G5, s.2.2)).1 = (progRO p Hb st c s).1 := by
  classical
  suffices e : @outPre (icPrg (rowFn s.2.2)) Hb CrtGen.tables st G5 (simulate p c) =
      @outPre (icPrg (rowFn s.2.2)) Hb CrtGen.tables st s.2.1 (simulate p c) by
    simp only [progRO, e]
  unfold progKeys5 at h
  unfold outPre
  split
  · rename_i b hb
    rw [hb] at h
    have hmu : st.mu1 (rec5 Hb G5) = st.mu1 (rec5 Hb s.2.1) := by rw [rec5_mu1, rec5_mu1]
    have h4 : (rec5 Hb G5).hash .h4 = (rec5 Hb s.2.1).hash .h4 := by rw [rec5_h4, rec5_h4]
    have hA : (rec5 Hb G5).AgreeOff .h5 (rec5 Hb s.2.1) := by
      intro k hk; rw [rec5_agree_ne hk, rec5_agree_ne hk]
    refine @vPre_h5_congr (icPrg (rowFn s.2.2)) _ _ hA _ _ _ fun x hx => ?_
    rw [@vIn5_congr (icPrg (rowFn s.2.2)) _ st _ _ hmu h4] at hx
    refine withTable_h5_congr _ fun _ => (h _ (mem_image.2 ⟨x, List.mem_toFinset.2 hx, rfl⟩)).symm
  · rfl

/-- **The programming reads the cipher only at `progKeysE`.** -/
theorem progRO_congrE (c : SimCoins p) (s : Sh p) (E : Cipher)
    (h : ∀ k ∈ progKeysE Hb st (simulate p c) s, s.2.2 k = E k) :
    (progRO p Hb st c (s.1, s.2.1, E)).1 = (progRO p Hb st c s).1 := by
  suffices e : @outPre (icPrg (rowFn E)) Hb CrtGen.tables st s.2.1 (simulate p c) =
      @outPre (icPrg (rowFn s.2.2)) Hb CrtGen.tables st s.2.1 (simulate p c) by
    simp only [progRO, e]
  unfold progKeysE at h
  unfold outPre
  split
  · rename_i b hb
    rw [hb] at h
    exact (vPre_ic_congr _ _ _ _ fun k hk => rowFn_congr (h k hk)).symm
  · rfl

/-- The programmed `H₂³` table is `simTab`'s. -/
lemma progRO_fst (st : Statement) (c : SimCoins st.params) (s : Sh st.params) :
    (progRO st.params Hb st c s).1 = @simTab (icPrg s.2.2) Hb CrtGen.tables st s.2.1
      (simulate st.params c) c.1.2.1 s.1 := rfl

lemma card_progKeysE (o : Except String ByteArray) (s : Sh p) :
    (progKeysE Hb st o s).card ≤ 4607 := by
  unfold progKeysE
  split
  · exact rdKeys_card _ _ _ _
  · simp

end Reads

/-! ## One proof, on one tape for both experiments -/

/-- **The error of `zk_rom_ic_h23_main_num`** without the (PU) term, at budgets `q₃`, `q_E`. -/
noncomputable def εS (q3 qE : ℕ) : ℝ :=
  q3 / 2 ^ 128 + 1 / 2 ^ 113 + 221 * (4607 + (qE + 4607)) / 2 ^ 128

lemma εS_nonneg (q3 qE : ℕ) : 0 ≤ εS q3 qE := by unfold εS; positivity

lemma εS_mono {q3 qE q3' qE' : ℕ} (h3 : q3 ≤ q3') (hE : qE ≤ qE') : εS q3 qE ≤ εS q3' qE' := by
  unfold εS
  have h3' : (q3 : ℝ) ≤ q3' := by exact_mod_cast h3
  have hE' : (qE : ℝ) ≤ qE' := by exact_mod_cast hE
  gcongr

/-- The coins of a proof slot: the prover's `ρ` and the simulator's coins (each experiment uses
one of them), and the proof's own tables. -/
abbrev KS (p : Params) := (Bytes 16 × SimCoins p) × VP p

section Slot

variable (Hb : Hashes) (st : Statement) (w : ByteArray)

/-- **Zero knowledge on `main` for one proof, on one tape** (`zk_rom_ic_h23_main_num`). The real
experiment (`realRO`, the proof's own `H₃` slice and `H₂³` table, the shared `H₅` table and cipher)
and the simulated one (`simulate`, the `H₂³` table programmed by `progRO`) are both run on the tape
`USh × KS p`; the distinguisher `D` reads the `H₃` slice and the cipher at `q₃`, `q_E` keys, `H₅`
at the explicit keys `Q5`, and `H₂³` freely. -/
theorem slot_zk_main {cs : ByteArray → ByteArray → System GF128} (hm : MainP st.params)
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
    |pr (USh × KS st.params) (fun z =>
        D (realRO st.params Hb st w z.2.1.1 z.2.2.1 (shOf z.2.2.2 z.1)) z.2.2.1 z.2.2.2 z.1.1 z.1.2) -
      pr (USh × KS st.params) (fun z =>
        D (simulate st.params z.2.1.2) z.2.2.1
          (progRO st.params Hb st z.2.1.2 (shOf z.2.2.2 z.1)).1 z.1.1 z.1.2)| ≤
      εS q3 qE + pr (USh × KS st.params) (fun z =>
        mainPredIC Hb st hm Q5 (wPre w) ((z.2.1.2, (z.2.2.1, z.2.2.2, z.1.1)), z.1.2)) := by
  have key := zk_rom_ic_h23_main_num Hb st w hm hzk hHb hp D Q3 hQ3 hq3 Q5 hQ5 QE hQE hqE
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
  have r3 : pr (USh × KS st.params) (fun z =>
        mainPredIC Hb st hm Q5 (wPre w) ((z.2.1.2, (z.2.2.1, z.2.2.2, z.1.1)), z.1.2)) =
      pr ((SimCoins st.params × Vis2 st.params) × Cipher) (mainPredIC Hb st hm Q5 (wPre w)) := by
    rw [← pr_equiv e2]
    exact pr_prod_fst (β := Bytes 16) (mainPredIC Hb st hm Q5 (wPre w))
  rw [r1, r2, r3]
  unfold εS
  exact key

end Slot

end VoleMole.ZK.Sim
