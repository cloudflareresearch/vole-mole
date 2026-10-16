import VoleMole.ZK.HopsH4Perm
import VoleMole.ZK.GrindNum

/-!
# Zero knowledge with AES as uniformly random permutations (`lean/docs/zk.md` §10.1)

`zk_rom_ic_h23` (`ZK/HopsIC.lean`) has the cipher of the whole BAVC and VOLE expansion a uniform
table of *functions* `E : Cipher`. Here it is a uniform table of **permutations**
`π : PCipher = Blk → Equiv.Perm Blk`: the executable prover and verifier run with the CTR PRG of
its rows (`icPrg (cf π)`), the simulator recomputes its grinding prefix with them, and the
distinguisher sees `π` itself and reads it at `q_E` keys (whole permutations: forward and inverse
queries).

The chain is `zk_rom_ic_h23`'s: the hops before and after H4 hold for every cipher, hence for the
rows of every `π` (`zk_pre_h4`, `zk_post_h4` at the instance `icPrg (cf π)`, averaged over `π`);
H4 is `hide_rom_query_perm` (`ZK/HopsH4Perm.lean`) with the distinguisher's and the honest
recomputation's reads (`viewICPm`, `viewKeysPm`, `joint3_h4_perm`).

**`zk_rom_ic_h23_num_perm`**: the advantage is at most

    q₃·2⁻¹²⁸ + 2⁻¹¹⁰ + 221·(4607 + q_E + 4607)/(2¹²⁸ − (nHi + 1)) + switchEps + (q₅ + 1)·2⁻¹²⁸,

`switchEps = (17·C(2 + VOLE_COL_BLOCKS, 2) + C(nHi + 1, 2))·2⁻¹²⁸` the PRP/PRF switching term of the
hidden leaves' and the root's rows.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy
  VoleMole.ZK.IC

/-! ## H4 with permutation rows, with the honest recomputation's reads -/

section ICPerm

variable (Hb : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)

/-- **The distinguisher's view after the programmed points are recomputed** (hybrid H3), with the
cipher the rows of the permutation table `π`, which the distinguisher also sees. -/
noncomputable def viewICPm (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F →
      PCipher → Prop) (a : Bytes 16) (g : Grind) (v : Vis2 st.params) (o : Hidden st.params)
    (π : PCipher) : Prop :=
  viewIC Hb T st w (fun o G3 G2 G5 _ => D o G3 G2 G5 π) a g v o (cf π)

/-- **The keys the view reads**: the distinguisher's and the honest recomputation's. -/
noncomputable def viewKeysPm (QE : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F →
      PCipher → Finset Blk) (a : Bytes 16) (g : Grind) (v : Vis2 st.params) (o : Hidden st.params)
    (π : PCipher) : Finset Blk :=
  viewKeys Hb T st w (fun o G3 G2 G5 _ => QE o G3 G2 G5 π) a g v o (cf π)

variable {Hb T st w}

/-- **The view reads the permutation table only at `viewKeysPm`.** -/
theorem viewICPm_congr {cs : ByteArray → ByteArray → System GF128} (hzk : ZKHyp T st w cs)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → PCipher → Prop)
    (QE : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → PCipher → Finset Blk)
    (hQE : ∀ o G3 G2 G5 π π', (∀ k ∈ QE o G3 G2 G5 π, π k = π' k) →
      (D o G3 G2 G5 π ↔ D o G3 G2 G5 π'))
    (a : Bytes 16) (g : Grind) (v : Vis2 st.params) (o : Hidden st.params) (π π' : PCipher)
    (hπ : ∀ k ∈ viewKeysPm Hb T st w QE a g v o π, π k = π' k) :
    viewICPm Hb T st w D a g v o π ↔ viewICPm Hb T st w D a g v o π' := by
  have s1 : viewICPm Hb T st w D a g v o π ↔
      viewIC Hb T st w (fun o G3 G2 G5 _ => D o G3 G2 G5 π') a g v o (cf π) := by
    unfold viewICPm viewIC Dp
    exact hQE _ _ _ _ _ _ fun k hk => hπ k (Finset.mem_union_left _ hk)
  have s2 := viewIC_congr hzk (fun o G3 G2 G5 _ => D o G3 G2 G5 π') (fun _ _ _ _ _ => ∅)
    (fun _ _ _ _ _ _ _ => Iff.rfl) a g v o (cf π) (cf π') (fun k hk => by
      have hk' : k ∈ viewKeysPm Hb T st w QE a g v o π := by
        unfold viewKeysPm viewKeys at *
        rcases Finset.mem_union.1 hk with h | h
        · exact absurd h (Finset.notMem_empty _)
        · exact Finset.mem_union_right _ h
      show ⇑(π k) = ⇑(π' k)
      rw [hπ k hk'])
  exact s1.trans s2

theorem viewKeysPm_card
    (QE : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → PCipher → Finset Blk)
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 π, (QE o G3 G2 G5 π).card ≤ qE) (a : Bytes 16) (g : Grind)
    (v : Vis2 st.params) (o : Hidden st.params) (π : PCipher) :
    (viewKeysPm Hb T st w QE a g v o π).card ≤ qE + 4607 :=
  viewKeys_card (fun o G3 G2 G5 _ => QE o G3 G2 G5 π) (fun o G3 G2 G5 _ => hqE o G3 G2 G5 π)
    a g v o (cf π)

variable (Hb T st w)

/-- **H4 with AES as random permutations, with the cipher in the whole prover and verifier**: the
hidden part computed with the rows of `π` from a uniform root seed, against the ideal hidden part,
with `π` uniform and seen by the distinguisher, who reads it at `q_E` keys; the honest recomputation
reads it at the reconstruction's `≤ 4607` keys, counted as reads (`hide_rom_query_perm`). -/
theorem joint3_h4_perm (hp : SmallParams st.params) {cs : ByteArray → ByteArray → System GF128}
    (hzk : ZKHyp T st w cs)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → PCipher → Prop)
    (QE : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → PCipher → Finset Blk)
    (hQE : ∀ o G3 G2 G5 π π', (∀ k ∈ QE o G3 G2 G5 π, π k = π' k) →
      (D o G3 G2 G5 π ↔ D o G3 G2 G5 π'))
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 π, (QE o G3 G2 G5 π).card ≤ qE) :
    |pr ((((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5F)) × PCipher)
        (fun c => @Dp (icPrg (cf c.2)) Hb T st (fun o G3 G2 G5 => D o G3 G2 G5 c.2)
          (@hyb3 (icPrg (cf c.2)) (recB Hb st w c.1.2.1 c.1.2.2) T st w (c.1.1.1.2, c.1.1.2.2)
            (@hiddenOut (icPrg (cf c.2)) st.params (ivOfPre Hb st c.1.1.1.2)
              (ba (deltaOf c.1.1.2.2)) c.1.1.1.1))
          c.1.1.2.2 (c.1.2.1, c.1.1.2.1, c.1.2.2)) -
      pr (((Hidden st.params × (Bytes 16 × Grind)) × Vis2 st.params) × PCipher) (fun c =>
        @Dp (icPrg (cf c.2)) Hb T st (fun o G3 G2 G5 => D o G3 G2 G5 c.2)
          (@hyb3 (icPrg (cf c.2)) (recB Hb st w c.1.2.1 c.1.2.2.2) T st w c.1.1.2
            (hiddenIdeal (ba (deltaOf c.1.1.2.2)) c.1.1.1)) c.1.1.2.2 c.1.2)| ≤
      221 * (4607 + (qE + 4607)) / ((2 ^ 128 - (nHi st.params + 1) : ℕ) : ℝ) +
        switchEps st.params := by
  let E2 : ((Bytes 16 × Grind) × Vis2 st.params) × (Blk × PCipher) ≃
      (((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5F)) × PCipher :=
    { toFun := fun c => ((((c.2.1, c.1.1.1), (c.1.2.2.1, c.1.1.2)), (c.1.2.1, c.1.2.2.2)), c.2.2)
      invFun := fun c => (((c.1.1.1.2, c.1.1.2.2), (c.1.2.1, c.1.1.2.1, c.1.2.2)), (c.1.1.1.1, c.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let E3 : ((Bytes 16 × Grind) × Vis2 st.params) × (Hidden st.params × PCipher) ≃
      ((Hidden st.params × (Bytes 16 × Grind)) × Vis2 st.params) × PCipher :=
    { toFun := fun c => (((c.2.1, c.1.1), c.1.2), c.2.2)
      invFun := fun c => ((c.1.1.2, c.1.2), (c.1.1.1, c.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv E2, ← pr_equiv E3]
  refine abs_pr_prod_sub_le _ _ fun x => ?_
  obtain ⟨⟨a, g⟩, v⟩ := x
  have h := hide_rom_query_perm st.params (ivOfPre Hb st a) (ba (deltaOf g)) hp
    (viewICPm Hb T st w D a g v) (viewKeysPm Hb T st w QE a g v)
    (fun o π π' hk => viewICPm_congr hzk D QE hQE a g v o π π' hk)
    (viewKeysPm_card QE hqE a g v)
  unfold IC.realPrPm IC.idealPrPm at h
  have e : pr (Blk × PCipher) (fun p => viewICPm Hb T st w D a g v
        (hiddenOutE (cf p.2) st.params (ivOfPre Hb st a) (ba (deltaOf g)) p.1) p.2) =
      pr (Blk × PCipher) (fun p => viewICPm Hb T st w D a g v
        (@hiddenOut (icPrg (cf p.2)) st.params (ivOfPre Hb st a) (ba (deltaOf g)) p.1) p.2) :=
    pr_congr fun p => by rw [hiddenOut_ic]
  rw [e] at h
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

end ICPerm

/-! ## The end-to-end statement -/

section MainPerm

variable (Hb : Hashes) (st : Statement) (w : ByteArray)

/-- **Zero knowledge in the random-oracle model with AES as uniformly random permutations**
(label-row layout, faest-arch-opt's tables, one statement and witness).

As `zk_rom_ic_h23`, with the cipher of the whole BAVC and VOLE expansion the rows of a uniform
table `π` of permutations of the blocks (`PCipher`): the real world is the executable prover
`Prover.prove` run with the CTR PRG of the rows of `π` (`icPrg (cf π)`), the simulator outputs
`simulate` and the `H₂³` table programmed at the grinding points it recomputes with the rows of
`π`. A distinguisher `D` sees the output, the three tables and `π`, reads `H₃`, `H₅` and `π`
adaptively at `q₃`, `q₅` and `q_E` keys (whole permutations at a key: forward and inverse
queries), and reads `H₂³` freely. Its advantage is at most

    q₃·2⁻¹²⁸ + Pr[GrindBad] + 221·(4607 + q_E + 4607)/(2¹²⁸ − (nHi + 1)) + switchEps
      + (q₅ + 1)·2⁻¹²⁸. -/
theorem zk_rom_ic_h23_perm {cs : ByteArray → ByteArray → System GF128}
    (hlr : st.params.labelRows = true)
    (hzk : ZKHyp CrtGen.tables st w cs) (hHb : HashesWF Hb) (hp : SmallParams st.params)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → PCipher → Prop)
    (Q3 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → PCipher → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G2 G5 π, (∀ k ∈ Q3 o G3 G2 G5 π, G3 k = G3' k) →
      (D o G3 G2 G5 π ↔ D o G3' G2 G5 π))
    {q3 : ℕ} (hq3 : ∀ o G3 G2 G5 π, (Q3 o G3 G2 G5 π).card ≤ q3)
    (Q5 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → PCipher → Finset (Bytes 37))
    (hQ5 : ∀ o G3 G2 G5 G5' π, (∀ k ∈ Q5 o G3 G2 G5 π, G5 k = G5' k) →
      (D o G3 G2 G5 π ↔ D o G3 G2 G5' π))
    {q5 : ℕ} (hq5 : ∀ o G3 G2 G5 π, (Q5 o G3 G2 G5 π).card ≤ q5)
    (QE : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → PCipher → Finset Blk)
    (hQE : ∀ o G3 G2 G5 π π', (∀ k ∈ QE o G3 G2 G5 π, π k = π' k) →
      (D o G3 G2 G5 π ↔ D o G3 G2 G5 π'))
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 π, (QE o G3 G2 G5 π).card ≤ qE) :
    |pr (((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × PCipher) (fun c =>
        D (@Prover.prove (icPrg (cf c.2)) (recH Hb st w c.1.2.1 c.1.1.2 c.1.2.2) CrtGen.tables st w
          (ba c.1.1.1) st.params.witnessBytes) c.1.2.1 c.1.1.2 c.1.2.2 c.2) -
      pr ((SimCoins st.params × Vis2 st.params) × PCipher) (fun c =>
        D (simulate st.params c.1.1) c.1.2.1
          (@simTab (icPrg (cf c.2)) Hb CrtGen.tables st c.1.2.2.2 (simulate st.params c.1.1)
            c.1.1.1.2.1 c.1.2.2.1) c.1.2.2.2 c.2)| ≤
      q3 / 2 ^ 128 + pr Grind (GrindBad CrtGen.tables) +
        (221 * (4607 + (qE + 4607)) / ((2 ^ 128 - (nHi st.params + 1) : ℕ) : ℝ) +
          switchEps st.params) + (q5 + 1) / 2 ^ 128 := by
  have hA := abs_pr_prod_sub_le'
    (fun (c : ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × PCipher) =>
      D (@Prover.prove (icPrg (cf c.2)) (recH Hb st w c.1.2.1 c.1.1.2 c.1.2.2) CrtGen.tables st w
        (ba c.1.1.1) st.params.witnessBytes) c.1.2.1 c.1.1.2 c.1.2.2 c.2)
    (fun (c : (((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5F)) × PCipher) =>
      @Dp (icPrg (cf c.2)) Hb CrtGen.tables st (fun o G3 G2 G5 => D o G3 G2 G5 c.2)
        (@hyb3 (icPrg (cf c.2)) (recB Hb st w c.1.2.1 c.1.2.2) CrtGen.tables st w
          (c.1.1.1.2, c.1.1.2.2)
          (@hiddenOut (icPrg (cf c.2)) st.params (ivOfPre Hb st c.1.1.1.2)
            (ba (deltaOf c.1.1.2.2)) c.1.1.1.1))
        c.1.1.2.2 (c.1.2.1, c.1.1.2.1, c.1.2.2))
    (fun π => @zk_pre_h4 (icPrg (cf π)) Hb st w cs hlr hzk hHb (fun o G3 G2 G5 => D o G3 G2 G5 π)
      (fun o G3 G2 G5 => Q3 o G3 G2 G5 π) (fun o G3 G3' G2 G5 => hQ3 o G3 G3' G2 G5 π) q3
      (fun o G3 G2 G5 => hq3 o G3 G2 G5 π))
  have hB := joint3_h4_perm Hb CrtGen.tables st w hp hzk D QE hQE hqE
  have hC := abs_pr_prod_sub_le'
    (fun (c : ((Hidden st.params × (Bytes 16 × Grind)) × Vis2 st.params) × PCipher) =>
      @Dp (icPrg (cf c.2)) Hb CrtGen.tables st (fun o G3 G2 G5 => D o G3 G2 G5 c.2)
        (@hyb3 (icPrg (cf c.2)) (recB Hb st w c.1.2.1 c.1.2.2.2) CrtGen.tables st w c.1.1.2
          (hiddenIdeal (ba (deltaOf c.1.1.2.2)) c.1.1.1)) c.1.1.2.2 c.1.2)
    (fun (c : (SimCoins st.params × Vis2 st.params) × PCipher) =>
      D (simulate st.params c.1.1) c.1.2.1
        (@simTab (icPrg (cf c.2)) Hb CrtGen.tables st c.1.2.2.2 (simulate st.params c.1.1)
          c.1.1.1.2.1 c.1.2.2.1) c.1.2.2.2 c.2)
    (fun π => @zk_post_h4 (icPrg (cf π)) Hb st w cs hlr hzk hHb (fun o G3 G2 G5 => D o G3 G2 G5 π)
      (fun o G3 G2 G5 => Q5 o G3 G2 G5 π) (fun o G3 G2 G5 G5' => hQ5 o G3 G2 G5 G5' π) q5
      (fun o G3 G2 G5 => hq5 o G3 G2 G5 π))
  refine (abs_sub_le _ _ _).trans ((add_le_add hA ((abs_sub_le _ _ _).trans
    (add_le_add hB hC))).trans (le_of_eq (by ring)))

/-- **`zk_rom_ic_h23_perm` with the grinding term numeric**: with AES as uniformly random
permutations (whole permutation rows read by the distinguisher), the executable prover is

    q₃·2⁻¹²⁸ + 2⁻¹¹⁰ + 221·(4607 + q_E + 4607)/(2¹²⁸ − (nHi + 1)) + switchEps + (q₅ + 1)·2⁻¹²⁸

close to the programming simulator. -/
theorem zk_rom_ic_h23_num_perm {cs : ByteArray → ByteArray → System GF128}
    (hlr : st.params.labelRows = true)
    (hzk : ZKHyp CrtGen.tables st w cs) (hHb : HashesWF Hb) (hp : SmallParams st.params)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → PCipher → Prop)
    (Q3 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → PCipher → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G2 G5 π, (∀ k ∈ Q3 o G3 G2 G5 π, G3 k = G3' k) →
      (D o G3 G2 G5 π ↔ D o G3' G2 G5 π))
    {q3 : ℕ} (hq3 : ∀ o G3 G2 G5 π, (Q3 o G3 G2 G5 π).card ≤ q3)
    (Q5 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → PCipher → Finset (Bytes 37))
    (hQ5 : ∀ o G3 G2 G5 G5' π, (∀ k ∈ Q5 o G3 G2 G5 π, G5 k = G5' k) →
      (D o G3 G2 G5 π ↔ D o G3 G2 G5' π))
    {q5 : ℕ} (hq5 : ∀ o G3 G2 G5 π, (Q5 o G3 G2 G5 π).card ≤ q5)
    (QE : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → PCipher → Finset Blk)
    (hQE : ∀ o G3 G2 G5 π π', (∀ k ∈ QE o G3 G2 G5 π, π k = π' k) →
      (D o G3 G2 G5 π ↔ D o G3 G2 G5 π'))
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 π, (QE o G3 G2 G5 π).card ≤ qE) :
    |pr (((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × PCipher) (fun c =>
        D (@Prover.prove (icPrg (cf c.2)) (recH Hb st w c.1.2.1 c.1.1.2 c.1.2.2) CrtGen.tables st w
          (ba c.1.1.1) st.params.witnessBytes) c.1.2.1 c.1.1.2 c.1.2.2 c.2) -
      pr ((SimCoins st.params × Vis2 st.params) × PCipher) (fun c =>
        D (simulate st.params c.1.1) c.1.2.1
          (@simTab (icPrg (cf c.2)) Hb CrtGen.tables st c.1.2.2.2 (simulate st.params c.1.1)
            c.1.1.1.2.1 c.1.2.2.1) c.1.2.2.2 c.2)| ≤
      q3 / 2 ^ 128 + 1 / 2 ^ 110 +
        (221 * (4607 + (qE + 4607)) / ((2 ^ 128 - (nHi st.params + 1) : ℕ) : ℝ) +
          switchEps st.params) + (q5 + 1) / 2 ^ 128 :=
  (zk_rom_ic_h23_perm Hb st w hlr hzk hHb hp D Q3 hQ3 hq3 Q5 hQ5 hq5 QE hQE hqE).trans
    (add_le_add (add_le_add (add_le_add le_rfl grindBad_le_110) le_rfl) le_rfl)

end MainPerm

end VoleMole.ZK.Sim
