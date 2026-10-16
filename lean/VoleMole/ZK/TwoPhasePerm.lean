import VoleMole.ZK.TwoPhaseAd
import VoleMole.ZK.ReadsROPerm

/-!
# Two-phase zero knowledge with AES as uniformly random permutations

`zk2_rom_ic_h23` (`ZK/TwoPhaseIC.lean`) and `zk2_rom_ic_h23A` (`ZK/TwoPhaseAd.lean`) have the
cipher a uniform table of *functions*. Here, as `zk_rom_ic_h23_perm` (`ZK/HopsICPerm.lean`) for the
single-phase prover, it is a uniform table `π : PCipher` of **permutations**: the two-phase run, the
simulator's `chal1` and its recomputation of the grinding prefix use the rows `cf π`, and the
distinguisher and the continuation read whole permutation rows (forward and inverse queries).

The chains are the function-row ones: the hops before and after H4 hold for every cipher
(`zk2_pre_h4`, `zk2_post_h4`, `zk2_pre_h4A`, `zk2_post_h4A` at the instance `icPrg (cf π)`,
averaged over `π`); H4 is `hide_rom_query_perm` with the distinguisher's, the honest
recomputation's and the continuation's reads (`viewIC2Pm`, `viewKeys2Pm`, `joint3_h4_2_perm`;
`viewIC2APm`, `viewKeys2APm`, `joint3_h4_2A_perm`, the continuation read at the output's step 1).

* **`zk2_rom_ic_h23_num_perm`**: the two-phase advantage is at most the single-phase
  `εROPm p q₃ (q₅ + q_k5) (q_E + q_kE)`.
* **`zk2_rom_ic_h23A_num_perm`**: with a continuation reading the tables after step 1,
  `εROPm p (q₃ + q_k3) (q₅ + q_k5) (q_E + q_kE)`.
* In the games' form (`ShPm p`): **`zk2_ro_perm`**, **`zk2_adaptive_perm`**, and the instances
  **`ZK2Row.perm`**, **`ZK2ARow.perm`**: PomFRIT's games (stated for every row type) hold with
  permutation rows.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

set_option linter.unusedSectionVars false

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy
  VoleMole.ZK.IC

/-! ## H4 with permutation rows, two phases -/

section IC2Pm

variable (Hb : Hashes) (st : Statement) (r : ByteArray) (K : Tab5F → PCipher → Cont2)

/-- **The two-phase view after the programmed points are recomputed** (hybrid H3), with the
cipher the rows of the permutation table `π`, which the distinguisher and the continuation see. -/
noncomputable def viewIC2Pm (D : Out2 → Tab3 → Tab2G st.params → Tab5F → PCipher → Prop)
    (a : Bytes 16) (g : Grind) (fb : Fallback st.params) (v : Vis2 st.params) (o : Hidden st.params)
    (π : PCipher) : Prop :=
  viewIC2 Hb st r (fun G5 _ => K G5 π) (fun o G3 G2 G5 _ => D o G3 G2 G5 π) a g fb v o (cf π)

/-- **The keys the view reads**: the distinguisher's, the honest recomputation's and the
continuation's. -/
noncomputable def viewKeys2Pm (QE : Out2 → Tab3 → Tab2G st.params → Tab5F → PCipher → Finset Blk)
    (QKE : Tab5F → PCipher → Finset Blk) (a : Bytes 16) (g : Grind) (fb : Fallback st.params)
    (v : Vis2 st.params) (o : Hidden st.params) (π : PCipher) : Finset Blk :=
  viewKeys2 Hb st r (fun G5 _ => K G5 π) (fun o G3 G2 G5 _ => QE o G3 G2 G5 π)
    (fun G5 _ => QKE G5 π) a g fb v o (cf π)

variable {Hb st r K}

/-- **The two-phase view reads the permutation table only at `viewKeys2Pm`.** -/
theorem viewIC2Pm_congr (hh : ∀ G5 π, Hyp2 st r (K G5 π))
    (QKE : Tab5F → PCipher → Finset Blk)
    (hQKE : ∀ G5 π π', (∀ key ∈ QKE G5 π, π key = π' key) → K G5 π = K G5 π')
    (D : Out2 → Tab3 → Tab2G st.params → Tab5F → PCipher → Prop)
    (QE : Out2 → Tab3 → Tab2G st.params → Tab5F → PCipher → Finset Blk)
    (hQE : ∀ o G3 G2 G5 π π', (∀ k ∈ QE o G3 G2 G5 π, π k = π' k) →
      (D o G3 G2 G5 π ↔ D o G3 G2 G5 π'))
    (a : Bytes 16) (g : Grind) (fb : Fallback st.params) (v : Vis2 st.params) (o : Hidden st.params)
    (π π' : PCipher) (hπ : ∀ k ∈ viewKeys2Pm Hb st r K QE QKE a g fb v o π, π k = π' k) :
    viewIC2Pm Hb st r K D a g fb v o π ↔ viewIC2Pm Hb st r K D a g fb v o π' := by
  have hK : K v.2.2 π = K v.2.2 π' :=
    hQKE v.2.2 π π' fun key hk => hπ key (Finset.mem_union_right _ hk)
  have s1 : viewIC2Pm Hb st r K D a g fb v o π ↔
      viewIC2 Hb st r (fun G5 _ => K G5 π) (fun o G3 G2 G5 _ => D o G3 G2 G5 π') a g fb v o
        (cf π) := by
    unfold viewIC2Pm viewIC2 Dp2
    exact hQE _ _ _ _ _ _ fun k hk => hπ k (Finset.mem_union_left _ (Finset.mem_union_left _ hk))
  have s2 := viewIC2_congr (st := st) (r := r) (K := fun G5 _ => K G5 π) (Hb := Hb)
    (fun G5 _ => hh G5 π) (fun _ _ => ∅) (fun _ _ _ _ => rfl)
    (fun o G3 G2 G5 _ => D o G3 G2 G5 π') (fun _ _ _ _ _ => ∅) (fun _ _ _ _ _ _ _ => Iff.rfl)
    a g fb v o (cf π) (cf π') (fun k hk => by
      have hk' : k ∈ viewKeys2Pm Hb st r K QE QKE a g fb v o π := by
        unfold viewKeys2Pm viewKeys2 at *
        rcases Finset.mem_union.1 hk with h | h
        · rcases Finset.mem_union.1 h with h | h
          · exact absurd h (Finset.notMem_empty _)
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
        · exact absurd h (Finset.notMem_empty _)
      show ⇑(π k) = ⇑(π' k)
      rw [hπ k hk'])
  have s3 : viewIC2 Hb st r (fun G5 _ => K G5 π) (fun o G3 G2 G5 _ => D o G3 G2 G5 π') a g fb v o
      (cf π') ↔ viewIC2Pm Hb st r K D a g fb v o π' := by
    unfold viewIC2Pm viewIC2
    dsimp only
    rw [hK]
  exact s1.trans (s2.trans s3)

theorem viewKeys2Pm_card
    (QE : Out2 → Tab3 → Tab2G st.params → Tab5F → PCipher → Finset Blk)
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 π, (QE o G3 G2 G5 π).card ≤ qE)
    (QKE : Tab5F → PCipher → Finset Blk) {qkE : ℕ} (hqkE : ∀ G5 π, (QKE G5 π).card ≤ qkE)
    (a : Bytes 16) (g : Grind) (fb : Fallback st.params) (v : Vis2 st.params) (o : Hidden st.params)
    (π : PCipher) :
    (viewKeys2Pm Hb st r K QE QKE a g fb v o π).card ≤ (qE + qkE) + 4607 :=
  viewKeys2_card (fun o G3 G2 G5 _ => QE o G3 G2 G5 π) (fun o G3 G2 G5 _ => hqE o G3 G2 G5 π)
    (fun G5 _ => QKE G5 π) (fun G5 _ => hqkE G5 π) a g fb v o (cf π)

variable (Hb st r K)

/-- **H4 with AES as random permutations, two phases**: the hidden part computed with the rows of
`π` from a uniform root seed against the ideal hidden part, `π` uniform and read by the
distinguisher at `q_E` keys, by the continuation at `q_kE` keys and by the honest recomputation at
`≤ 4607` keys (`hide_rom_query_perm`). -/
theorem joint3_h4_2_perm (hp : SmallParams st.params) (hh : ∀ G5 π, Hyp2 st r (K G5 π))
    (QKE : Tab5F → PCipher → Finset Blk)
    (hQKE : ∀ G5 π π', (∀ key ∈ QKE G5 π, π key = π' key) → K G5 π = K G5 π')
    {qkE : ℕ} (hqkE : ∀ G5 π, (QKE G5 π).card ≤ qkE)
    (D : Out2 → Tab3 → Tab2G st.params → Tab5F → PCipher → Prop)
    (QE : Out2 → Tab3 → Tab2G st.params → Tab5F → PCipher → Finset Blk)
    (hQE : ∀ o G3 G2 G5 π π', (∀ k ∈ QE o G3 G2 G5 π, π k = π' k) →
      (D o G3 G2 G5 π ↔ D o G3 G2 G5 π'))
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 π, (QE o G3 G2 G5 π).card ≤ qE) :
    |pr (((((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × Fallback st.params) ×
          (Tab3 × Tab5F)) × PCipher)
        (fun c => @Dp2 (icPrg (cf c.2)) Hb CrtGen.tables st (K c.1.2.2 c.2)
          (fun o G3 G2 G5 => D o G3 G2 G5 c.2)
          (@hyb3' (icPrg (cf c.2)) (recB Hb (st1 st) r c.1.2.1 c.1.2.2) CrtGen.tables st r
            (K c.1.2.2 c.2) ((c.1.1.1.1.2, c.1.1.1.2.2), c.1.1.2)
            (@hiddenOut (icPrg (cf c.2)) st.params (ivOfPre Hb (st1 st) c.1.1.1.1.2)
              (ba (deltaOf c.1.1.1.2.2)) c.1.1.1.1.1))
          c.1.1.1.2.2 (c.1.2.1, c.1.1.1.2.1, c.1.2.2)) -
      pr (((Hidden st.params × ((Bytes 16 × Grind) × Fallback st.params)) × Vis2 st.params) ×
          PCipher) (fun c =>
        @Dp2 (icPrg (cf c.2)) Hb CrtGen.tables st (K c.1.2.2.2 c.2)
          (fun o G3 G2 G5 => D o G3 G2 G5 c.2)
          (@hyb3' (icPrg (cf c.2)) (recB Hb (st1 st) r c.1.2.1 c.1.2.2.2) CrtGen.tables st r
            (K c.1.2.2.2 c.2) c.1.1.2 (hiddenIdeal (ba (deltaOf c.1.1.2.1.2)) c.1.1.1)) c.1.1.2.1.2
          c.1.2)| ≤
      221 * (4607 + ((qE + qkE : ℕ) + 4607)) / ((2 ^ 128 - (nHi st.params + 1) : ℕ) : ℝ) +
        switchEps st.params := by
  let E2 : (((Bytes 16 × Grind) × Fallback st.params) × Vis2 st.params) × (Blk × PCipher) ≃
      ((((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × Fallback st.params) ×
        (Tab3 × Tab5F)) × PCipher :=
    { toFun := fun c => (((((c.2.1, c.1.1.1.1), (c.1.2.2.1, c.1.1.1.2)), c.1.1.2),
        (c.1.2.1, c.1.2.2.2)), c.2.2)
      invFun := fun c => ((((c.1.1.1.1.2, c.1.1.1.2.2), c.1.1.2), (c.1.2.1, c.1.1.1.2.1, c.1.2.2)),
        (c.1.1.1.1.1, c.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let E3 : (((Bytes 16 × Grind) × Fallback st.params) × Vis2 st.params) ×
      (Hidden st.params × PCipher) ≃
      ((Hidden st.params × ((Bytes 16 × Grind) × Fallback st.params)) × Vis2 st.params) ×
        PCipher :=
    { toFun := fun c => (((c.2.1, c.1.1), c.1.2), c.2.2)
      invFun := fun c => ((c.1.1.2, c.1.2), (c.1.1.1, c.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv E2, ← pr_equiv E3]
  refine abs_pr_prod_sub_le _ _ fun x => ?_
  obtain ⟨⟨⟨a, g⟩, fb⟩, v⟩ := x
  have h := hide_rom_query_perm st.params (ivOfPre Hb (st1 st) a) (ba (deltaOf g)) hp
    (viewIC2Pm Hb st r K D a g fb v) (viewKeys2Pm Hb st r K QE QKE a g fb v)
    (fun o π π' hk => viewIC2Pm_congr hh QKE hQKE D QE hQE a g fb v o π π' hk)
    (viewKeys2Pm_card QE hqE QKE hqkE a g fb v)
  unfold IC.realPrPm IC.idealPrPm at h
  have e : pr (Blk × PCipher) (fun p => viewIC2Pm Hb st r K D a g fb v
        (hiddenOutE (cf p.2) st.params (ivOfPre Hb (st1 st) a) (ba (deltaOf g)) p.1) p.2) =
      pr (Blk × PCipher) (fun p => viewIC2Pm Hb st r K D a g fb v
        (@hiddenOut (icPrg (cf p.2)) st.params (ivOfPre Hb (st1 st) a) (ba (deltaOf g)) p.1)
          p.2) :=
    pr_congr fun p => by rw [hiddenOut_ic]
  rw [e] at h
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

end IC2Pm

/-! ## The end-to-end statement, two phases -/

section Main2Pm

variable (Hb : Hashes) (st : Statement) (r : ByteArray) (K : Tab5F → PCipher → Cont2)

/-- **Two-phase zero knowledge in the random-oracle model with AES as uniformly random
permutations** (`zk2_rom_ic_h23` with the cipher the rows of a uniform permutation table `π`,
which the distinguisher and the continuation `K G5 π` read as whole permutations). The advantage
is at most

    q₃·2⁻¹²⁸ + Pr[GrindBad] + 221·(4607 + (q_E + q_kE) + 4607)/(2¹²⁸ − (nHi + 1)) + switchEps
      + ((q₅ + q_k5) + 1)·2⁻¹²⁸. -/
theorem zk2_rom_ic_h23_perm (hh : ∀ G5 π, Hyp2 st r (K G5 π)) (hHb : HashesWF Hb)
    (hp : SmallParams st.params)
    (QK5 : Tab5F → PCipher → Finset (Bytes 37))
    (hQK5 : ∀ G5 G5' π, (∀ key ∈ QK5 G5 π, G5 key = G5' key) → K G5 π = K G5' π)
    {qk5 : ℕ} (hqk5 : ∀ G5 π, (QK5 G5 π).card ≤ qk5)
    (QKE : Tab5F → PCipher → Finset Blk)
    (hQKE : ∀ G5 π π', (∀ key ∈ QKE G5 π, π key = π' key) → K G5 π = K G5 π')
    {qkE : ℕ} (hqkE : ∀ G5 π, (QKE G5 π).card ≤ qkE)
    (D : Out2 → Tab3 → Tab2G st.params → Tab5F → PCipher → Prop)
    (Q3 : Out2 → Tab3 → Tab2G st.params → Tab5F → PCipher → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G2 G5 π, (∀ k ∈ Q3 o G3 G2 G5 π, G3 k = G3' k) →
      (D o G3 G2 G5 π ↔ D o G3' G2 G5 π))
    {q3 : ℕ} (hq3 : ∀ o G3 G2 G5 π, (Q3 o G3 G2 G5 π).card ≤ q3)
    (Q5 : Out2 → Tab3 → Tab2G st.params → Tab5F → PCipher → Finset (Bytes 37))
    (hQ5 : ∀ o G3 G2 G5 G5' π, (∀ k ∈ Q5 o G3 G2 G5 π, G5 k = G5' k) →
      (D o G3 G2 G5 π ↔ D o G3 G2 G5' π))
    {q5 : ℕ} (hq5 : ∀ o G3 G2 G5 π, (Q5 o G3 G2 G5 π).card ≤ q5)
    (QE : Out2 → Tab3 → Tab2G st.params → Tab5F → PCipher → Finset Blk)
    (hQE : ∀ o G3 G2 G5 π π', (∀ k ∈ QE o G3 G2 G5 π, π k = π' k) →
      (D o G3 G2 G5 π ↔ D o G3 G2 G5 π'))
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 π, (QE o G3 G2 G5 π).card ≤ qE) :
    |pr (((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × PCipher) (fun c =>
        D (@realRun2 (icPrg (cf c.2)) (recH Hb (st1 st) r c.1.2.1 c.1.1.2 c.1.2.2) CrtGen.tables
          st r (K c.1.2.2 c.2) (ba c.1.1.1)) c.1.2.1 c.1.1.2 c.1.2.2 c.2) -
      pr ((SimCoins2 st.params × Vis2 st.params) × PCipher) (fun c =>
        D (@simRun2 (icPrg (cf c.2)) Hb st r.size (K c.1.2.2.2 c.2) c.1.1) c.1.2.1
          (@simTab2 (icPrg (cf c.2)) Hb CrtGen.tables st (K c.1.2.2.2 c.2) c.1.2.2.2
            (@simRun2 (icPrg (cf c.2)) Hb st r.size (K c.1.2.2.2 c.2) c.1.1) c.1.1.1.1.2.1
              c.1.2.2.1)
          c.1.2.2.2 c.2)| ≤
      q3 / 2 ^ 128 + pr Grind (GrindBad CrtGen.tables) +
        (221 * (4607 + ((qE + qkE : ℕ) + 4607)) / ((2 ^ 128 - (nHi st.params + 1) : ℕ) : ℝ) +
          switchEps st.params) + ((q5 + qk5 : ℕ) + 1) / 2 ^ 128 := by
  have hA := abs_pr_prod_sub_le'
    (fun (c : ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × PCipher) =>
      D (@realRun2 (icPrg (cf c.2)) (recH Hb (st1 st) r c.1.2.1 c.1.1.2 c.1.2.2) CrtGen.tables st r
        (K c.1.2.2 c.2) (ba c.1.1.1)) c.1.2.1 c.1.1.2 c.1.2.2 c.2)
    (fun (c : ((((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × Fallback st.params) ×
        (Tab3 × Tab5F)) × PCipher) =>
      @Dp2 (icPrg (cf c.2)) Hb CrtGen.tables st (K c.1.2.2 c.2) (fun o G3 G2 G5 => D o G3 G2 G5 c.2)
        (@hyb3' (icPrg (cf c.2)) (recB Hb (st1 st) r c.1.2.1 c.1.2.2) CrtGen.tables st r
          (K c.1.2.2 c.2) ((c.1.1.1.1.2, c.1.1.1.2.2), c.1.1.2)
          (@hiddenOut (icPrg (cf c.2)) st.params (ivOfPre Hb (st1 st) c.1.1.1.1.2)
            (ba (deltaOf c.1.1.1.2.2)) c.1.1.1.1.1))
        c.1.1.1.2.2 (c.1.2.1, c.1.1.1.2.1, c.1.2.2))
    (fun π => @zk2_pre_h4 (icPrg (cf π)) Hb st r (fun G5 => K G5 π) hHb (fun G5 => hh G5 π)
      (fun o G3 G2 G5 => D o G3 G2 G5 π)
      (fun o G3 G2 G5 => Q3 o G3 G2 G5 π) (fun o G3 G3' G2 G5 => hQ3 o G3 G3' G2 G5 π) q3
      (fun o G3 G2 G5 => hq3 o G3 G2 G5 π))
  have hB := joint3_h4_2_perm Hb st r K hp hh QKE hQKE hqkE D QE hQE hqE
  have hC := abs_pr_prod_sub_le'
    (fun (c : ((Hidden st.params × ((Bytes 16 × Grind) × Fallback st.params)) × Vis2 st.params) ×
        PCipher) =>
      @Dp2 (icPrg (cf c.2)) Hb CrtGen.tables st (K c.1.2.2.2 c.2)
        (fun o G3 G2 G5 => D o G3 G2 G5 c.2)
        (@hyb3' (icPrg (cf c.2)) (recB Hb (st1 st) r c.1.2.1 c.1.2.2.2) CrtGen.tables st r
          (K c.1.2.2.2 c.2) c.1.1.2 (hiddenIdeal (ba (deltaOf c.1.1.2.1.2)) c.1.1.1)) c.1.1.2.1.2
        c.1.2)
    (fun (c : (SimCoins2 st.params × Vis2 st.params) × PCipher) =>
      D (@simRun2 (icPrg (cf c.2)) Hb st r.size (K c.1.2.2.2 c.2) c.1.1) c.1.2.1
        (@simTab2 (icPrg (cf c.2)) Hb CrtGen.tables st (K c.1.2.2.2 c.2) c.1.2.2.2
          (@simRun2 (icPrg (cf c.2)) Hb st r.size (K c.1.2.2.2 c.2) c.1.1) c.1.1.1.1.2.1 c.1.2.2.1)
        c.1.2.2.2 c.2)
    (fun π => @zk2_post_h4 (icPrg (cf π)) Hb st r (fun G5 => K G5 π) hHb (fun G5 => hh G5 π)
      (fun G5 => QK5 G5 π) (fun G5 G5' => hQK5 G5 G5' π) qk5 (fun G5 => hqk5 G5 π)
      (fun o G3 G2 G5 => D o G3 G2 G5 π)
      (fun o G3 G2 G5 => Q5 o G3 G2 G5 π) (fun o G3 G2 G5 G5' => hQ5 o G3 G2 G5 G5' π) q5
      (fun o G3 G2 G5 => hq5 o G3 G2 G5 π))
  refine (abs_sub_le _ _ _).trans ((add_le_add hA ((abs_sub_le _ _ _).trans
    (add_le_add hB hC))).trans (le_of_eq (by push_cast; ring)))

/-- **`zk2_rom_ic_h23_perm` with `Pr[GrindBad] ≤ 2⁻¹¹⁰`**: the two-phase error with AES as random
permutations is the single-phase one, `εROPm p q₃ (q₅ + q_k5) (q_E + q_kE)`. -/
theorem zk2_rom_ic_h23_num_perm (hh : ∀ G5 π, Hyp2 st r (K G5 π)) (hHb : HashesWF Hb)
    (hp : SmallParams st.params)
    (QK5 : Tab5F → PCipher → Finset (Bytes 37))
    (hQK5 : ∀ G5 G5' π, (∀ key ∈ QK5 G5 π, G5 key = G5' key) → K G5 π = K G5' π)
    {qk5 : ℕ} (hqk5 : ∀ G5 π, (QK5 G5 π).card ≤ qk5)
    (QKE : Tab5F → PCipher → Finset Blk)
    (hQKE : ∀ G5 π π', (∀ key ∈ QKE G5 π, π key = π' key) → K G5 π = K G5 π')
    {qkE : ℕ} (hqkE : ∀ G5 π, (QKE G5 π).card ≤ qkE)
    (D : Out2 → Tab3 → Tab2G st.params → Tab5F → PCipher → Prop)
    (Q3 : Out2 → Tab3 → Tab2G st.params → Tab5F → PCipher → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G2 G5 π, (∀ k ∈ Q3 o G3 G2 G5 π, G3 k = G3' k) →
      (D o G3 G2 G5 π ↔ D o G3' G2 G5 π))
    {q3 : ℕ} (hq3 : ∀ o G3 G2 G5 π, (Q3 o G3 G2 G5 π).card ≤ q3)
    (Q5 : Out2 → Tab3 → Tab2G st.params → Tab5F → PCipher → Finset (Bytes 37))
    (hQ5 : ∀ o G3 G2 G5 G5' π, (∀ k ∈ Q5 o G3 G2 G5 π, G5 k = G5' k) →
      (D o G3 G2 G5 π ↔ D o G3 G2 G5' π))
    {q5 : ℕ} (hq5 : ∀ o G3 G2 G5 π, (Q5 o G3 G2 G5 π).card ≤ q5)
    (QE : Out2 → Tab3 → Tab2G st.params → Tab5F → PCipher → Finset Blk)
    (hQE : ∀ o G3 G2 G5 π π', (∀ k ∈ QE o G3 G2 G5 π, π k = π' k) →
      (D o G3 G2 G5 π ↔ D o G3 G2 G5 π'))
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 π, (QE o G3 G2 G5 π).card ≤ qE) :
    |pr (((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × PCipher) (fun c =>
        D (@realRun2 (icPrg (cf c.2)) (recH Hb (st1 st) r c.1.2.1 c.1.1.2 c.1.2.2) CrtGen.tables
          st r (K c.1.2.2 c.2) (ba c.1.1.1)) c.1.2.1 c.1.1.2 c.1.2.2 c.2) -
      pr ((SimCoins2 st.params × Vis2 st.params) × PCipher) (fun c =>
        D (@simRun2 (icPrg (cf c.2)) Hb st r.size (K c.1.2.2.2 c.2) c.1.1) c.1.2.1
          (@simTab2 (icPrg (cf c.2)) Hb CrtGen.tables st (K c.1.2.2.2 c.2) c.1.2.2.2
            (@simRun2 (icPrg (cf c.2)) Hb st r.size (K c.1.2.2.2 c.2) c.1.1) c.1.1.1.1.2.1
              c.1.2.2.1)
          c.1.2.2.2 c.2)| ≤
      εROPm st.params q3 (q5 + qk5) (qE + qkE) := by
  refine (zk2_rom_ic_h23_perm Hb st r K hh hHb hp QK5 hQK5 hqk5 QKE hQKE hqkE D Q3 hQ3 hq3 Q5 hQ5
    hq5 QE hQE hqE).trans ?_
  have := grindBad_le_110
  unfold εROPm
  push_cast
  linarith

end Main2Pm

/-! ## H4 with permutation rows, the continuation reading the tables after step 1 -/

section IC2APm

variable (Hb : Hashes) (st : Statement) (r : ByteArray) (K : Tab3 → Tab5F → PCipher → Cont2)

/-- **The two-phase view after the programmed points are recomputed**, the continuation
`K G3 G5 π` reading the permutation table. -/
noncomputable def viewIC2APm (D : Out2 → Tab3 → Tab2G st.params → Tab5F → PCipher → Prop)
    (a : Bytes 16) (g : Grind) (fb : Fallback st.params) (v : Vis2 st.params) (o : Hidden st.params)
    (π : PCipher) : Prop :=
  viewIC2A Hb st r (fun G3 G5 _ => K G3 G5 π) (fun o G3 G2 G5 _ => D o G3 G2 G5 π) a g fb v o
    (cf π)

/-- **The keys the view reads**: the distinguisher's, the honest recomputation's and the
continuation's at the output's step 1. -/
noncomputable def viewKeys2APm
    (QE : Out2 → Tab3 → Tab2G st.params → Tab5F → PCipher → Finset Blk)
    (QKE : ByteArray × ByteArray → Tab3 → Tab5F → PCipher → Finset Blk) (a : Bytes 16) (g : Grind)
    (fb : Fallback st.params) (v : Vis2 st.params) (o : Hidden st.params) (π : PCipher) :
    Finset Blk :=
  viewKeys2A Hb st r (fun G3 G5 _ => K G3 G5 π) (fun o G3 G2 G5 _ => QE o G3 G2 G5 π)
    (fun o1 G3 G5 _ => QKE o1 G3 G5 π) a g fb v o (cf π)

/-- **The two-phase view reads its continuation only at its step-1 output** (for a fixed
cipher). -/
theorem viewIC2A_kcongr {K₁ K₂ : Tab3 → Tab5F → Cipher → Cont2}
    (D : Out2 → Tab3 → Tab2G st.params → Tab5F → Cipher → Prop) (a : Bytes 16) (g : Grind)
    (fb : Fallback st.params) (v : Vis2 st.params) (o : Hidden st.params) (E : Cipher)
    (h : K₁ v.1 v.2.2 E ((@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r
        (K₁ v.1 v.2.2 E) ((a, g), fb) o).1,
      (@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r (K₁ v.1 v.2.2 E)
        ((a, g), fb) o).2.1) =
      K₂ v.1 v.2.2 E ((@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r
        (K₁ v.1 v.2.2 E) ((a, g), fb) o).1,
      (@hyb3' (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r (K₁ v.1 v.2.2 E)
        ((a, g), fb) o).2.1)) :
    viewIC2A Hb st r K₁ D a g fb v o E ↔ viewIC2A Hb st r K₂ D a g fb v o E := by
  have hout := @hyb3'_kcongr (icPrg E) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r _ _
    ((a, g), fb) o h
  unfold viewIC2A Dp2
  rw [← hout]
  unfold simTab2
  rw [@outPre2_kcongr' (icPrg E) Hb CrtGen.tables st _ _ v.2.2 _ h]

variable {Hb st r K}

/-- **The two-phase view reads the permutation table only at `viewKeys2APm`.** -/
theorem viewIC2APm_congr (hh : ∀ G3 G5 π, Hyp2 st r (K G3 G5 π))
    (QKE : ByteArray × ByteArray → Tab3 → Tab5F → PCipher → Finset Blk)
    (hQKE : ∀ o1 G3 G5 π π', (∀ key ∈ QKE o1 G3 G5 π, π key = π' key) →
      K G3 G5 π' o1 = K G3 G5 π o1)
    (D : Out2 → Tab3 → Tab2G st.params → Tab5F → PCipher → Prop)
    (QE : Out2 → Tab3 → Tab2G st.params → Tab5F → PCipher → Finset Blk)
    (hQE : ∀ o G3 G2 G5 π π', (∀ k ∈ QE o G3 G2 G5 π, π k = π' k) →
      (D o G3 G2 G5 π ↔ D o G3 G2 G5 π'))
    (a : Bytes 16) (g : Grind) (fb : Fallback st.params) (v : Vis2 st.params) (o : Hidden st.params)
    (π π' : PCipher) (hπ : ∀ k ∈ viewKeys2APm Hb st r K QE QKE a g fb v o π, π k = π' k) :
    viewIC2APm Hb st r K D a g fb v o π ↔ viewIC2APm Hb st r K D a g fb v o π' := by
  -- The honest reads agree.
  have hrd : ∀ key ∈ hRd (cf π) (recB Hb (st1 st) r v.1 v.2.2) (st1 st) (a, g, o.1, o.2.1)
      (deltaOf g), cf π key = cf π' key := fun key hk => by
    have hk' : key ∈ viewKeys2APm Hb st r K QE QKE a g fb v o π :=
      Finset.mem_union_left _ (Finset.mem_union_right _ hk)
    show ⇑(π key) = ⇑(π' key)
    rw [hπ key hk']
  -- The step-1 output, at `π` and at `π'` (it does not read the continuation).
  have hout : @hyb3' (icPrg (cf π)) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r
      (K v.1 v.2.2 π) ((a, g), fb) o =
      @hyb3' (icPrg (cf π')) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r (K v.1 v.2.2 π)
        ((a, g), fb) o :=
    hyb3'_ic_congr _ CrtGen.tables st r (K v.1 v.2.2 π) ((a, g), fb) o hrd
  have hK : K v.1 v.2.2 π' ((@hyb3' (icPrg (cf π)) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r
      (K v.1 v.2.2 π) ((a, g), fb) o).1, (@hyb3' (icPrg (cf π)) (recB Hb (st1 st) r v.1 v.2.2)
        CrtGen.tables st r (K v.1 v.2.2 π) ((a, g), fb) o).2.1) =
      K v.1 v.2.2 π ((@hyb3' (icPrg (cf π)) (recB Hb (st1 st) r v.1 v.2.2) CrtGen.tables st r
        (K v.1 v.2.2 π) ((a, g), fb) o).1, (@hyb3' (icPrg (cf π)) (recB Hb (st1 st) r v.1 v.2.2)
          CrtGen.tables st r (K v.1 v.2.2 π) ((a, g), fb) o).2.1) :=
    hQKE _ v.1 v.2.2 π π' fun key hk => hπ key (by
      unfold viewKeys2APm viewKeys2A
      beta_reduce
      exact Finset.mem_union_right _ hk)
  -- The distinguisher's table, then the cipher of the view, then the continuation.
  have s1 : viewIC2APm Hb st r K D a g fb v o π ↔
      viewIC2A Hb st r (fun G3 G5 _ => K G3 G5 π) (fun o G3 G2 G5 _ => D o G3 G2 G5 π') a g fb v o
        (cf π) := by
    unfold viewIC2APm viewIC2A Dp2
    exact hQE _ _ _ _ _ _ fun k hk => hπ k (Finset.mem_union_left _ (Finset.mem_union_left _ hk))
  have s2 := viewIC2A_congr (st := st) (r := r) (K := fun G3 G5 _ => K G3 G5 π) (Hb := Hb)
    (fun G3 G5 _ => hh G3 G5 π) (fun _ _ _ _ => ∅) (fun _ _ _ _ _ _ => rfl)
    (fun o G3 G2 G5 _ => D o G3 G2 G5 π') (fun _ _ _ _ _ => ∅) (fun _ _ _ _ _ _ _ => Iff.rfl)
    a g fb v o (cf π) (cf π') (fun k hk => by
      unfold viewKeys2A at hk
      rcases Finset.mem_union.1 hk with h | h
      · rcases Finset.mem_union.1 h with h | h
        · exact absurd h (Finset.notMem_empty _)
        · exact hrd k h
      · exact absurd h (Finset.notMem_empty _))
  have s3 : viewIC2A Hb st r (fun G3 G5 _ => K G3 G5 π) (fun o G3 G2 G5 _ => D o G3 G2 G5 π') a g
      fb v o (cf π') ↔ viewIC2APm Hb st r K D a g fb v o π' := by
    refine viewIC2A_kcongr Hb st r _ a g fb v o (cf π') ?_
    rw [← hout]
    exact hK.symm
  exact s1.trans (s2.trans s3)

theorem viewKeys2APm_card
    (QE : Out2 → Tab3 → Tab2G st.params → Tab5F → PCipher → Finset Blk)
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 π, (QE o G3 G2 G5 π).card ≤ qE)
    (QKE : ByteArray × ByteArray → Tab3 → Tab5F → PCipher → Finset Blk) {qkE : ℕ}
    (hqkE : ∀ o1 G3 G5 π, (QKE o1 G3 G5 π).card ≤ qkE)
    (a : Bytes 16) (g : Grind) (fb : Fallback st.params) (v : Vis2 st.params) (o : Hidden st.params)
    (π : PCipher) :
    (viewKeys2APm Hb st r K QE QKE a g fb v o π).card ≤ (qE + qkE) + 4607 :=
  viewKeys2A_card (fun o G3 G2 G5 _ => QE o G3 G2 G5 π) (fun o G3 G2 G5 _ => hqE o G3 G2 G5 π)
    (fun o1 G3 G5 _ => QKE o1 G3 G5 π) (fun o1 G3 G5 _ => hqkE o1 G3 G5 π) a g fb v o (cf π)

variable (Hb st r K)

/-- **H4 with AES as random permutations, two phases, the continuation reading the table at step
1's output** (`joint3_h4_2A` with `hide_rom_query_perm`). -/
theorem joint3_h4_2A_perm (hp : SmallParams st.params) (hh : ∀ G3 G5 π, Hyp2 st r (K G3 G5 π))
    (QKE : ByteArray × ByteArray → Tab3 → Tab5F → PCipher → Finset Blk)
    (hQKE : ∀ o1 G3 G5 π π', (∀ key ∈ QKE o1 G3 G5 π, π key = π' key) →
      K G3 G5 π' o1 = K G3 G5 π o1)
    {qkE : ℕ} (hqkE : ∀ o1 G3 G5 π, (QKE o1 G3 G5 π).card ≤ qkE)
    (D : Out2 → Tab3 → Tab2G st.params → Tab5F → PCipher → Prop)
    (QE : Out2 → Tab3 → Tab2G st.params → Tab5F → PCipher → Finset Blk)
    (hQE : ∀ o G3 G2 G5 π π', (∀ k ∈ QE o G3 G2 G5 π, π k = π' k) →
      (D o G3 G2 G5 π ↔ D o G3 G2 G5 π'))
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 π, (QE o G3 G2 G5 π).card ≤ qE) :
    |pr (((((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × Fallback st.params) ×
          (Tab3 × Tab5F)) × PCipher)
        (fun c => @Dp2 (icPrg (cf c.2)) Hb CrtGen.tables st (K c.1.2.1 c.1.2.2 c.2)
          (fun o G3 G2 G5 => D o G3 G2 G5 c.2)
          (@hyb3' (icPrg (cf c.2)) (recB Hb (st1 st) r c.1.2.1 c.1.2.2) CrtGen.tables st r
            (K c.1.2.1 c.1.2.2 c.2) ((c.1.1.1.1.2, c.1.1.1.2.2), c.1.1.2)
            (@hiddenOut (icPrg (cf c.2)) st.params (ivOfPre Hb (st1 st) c.1.1.1.1.2)
              (ba (deltaOf c.1.1.1.2.2)) c.1.1.1.1.1))
          c.1.1.1.2.2 (c.1.2.1, c.1.1.1.2.1, c.1.2.2)) -
      pr (((Hidden st.params × ((Bytes 16 × Grind) × Fallback st.params)) × Vis2 st.params) ×
          PCipher) (fun c =>
        @Dp2 (icPrg (cf c.2)) Hb CrtGen.tables st (K c.1.2.1 c.1.2.2.2 c.2)
          (fun o G3 G2 G5 => D o G3 G2 G5 c.2)
          (@hyb3' (icPrg (cf c.2)) (recB Hb (st1 st) r c.1.2.1 c.1.2.2.2) CrtGen.tables st r
            (K c.1.2.1 c.1.2.2.2 c.2) c.1.1.2 (hiddenIdeal (ba (deltaOf c.1.1.2.1.2)) c.1.1.1))
          c.1.1.2.1.2 c.1.2)| ≤
      221 * (4607 + ((qE + qkE : ℕ) + 4607)) / ((2 ^ 128 - (nHi st.params + 1) : ℕ) : ℝ) +
        switchEps st.params := by
  let E2 : (((Bytes 16 × Grind) × Fallback st.params) × Vis2 st.params) × (Blk × PCipher) ≃
      ((((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × Fallback st.params) ×
        (Tab3 × Tab5F)) × PCipher :=
    { toFun := fun c => (((((c.2.1, c.1.1.1.1), (c.1.2.2.1, c.1.1.1.2)), c.1.1.2),
        (c.1.2.1, c.1.2.2.2)), c.2.2)
      invFun := fun c => ((((c.1.1.1.1.2, c.1.1.1.2.2), c.1.1.2), (c.1.2.1, c.1.1.1.2.1, c.1.2.2)),
        (c.1.1.1.1.1, c.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let E3 : (((Bytes 16 × Grind) × Fallback st.params) × Vis2 st.params) ×
      (Hidden st.params × PCipher) ≃
      ((Hidden st.params × ((Bytes 16 × Grind) × Fallback st.params)) × Vis2 st.params) ×
        PCipher :=
    { toFun := fun c => (((c.2.1, c.1.1), c.1.2), c.2.2)
      invFun := fun c => ((c.1.1.2, c.1.2), (c.1.1.1, c.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv E2, ← pr_equiv E3]
  refine abs_pr_prod_sub_le _ _ fun x => ?_
  obtain ⟨⟨⟨a, g⟩, fb⟩, v⟩ := x
  have h := hide_rom_query_perm st.params (ivOfPre Hb (st1 st) a) (ba (deltaOf g)) hp
    (viewIC2APm Hb st r K D a g fb v) (viewKeys2APm Hb st r K QE QKE a g fb v)
    (fun o π π' hk => viewIC2APm_congr hh QKE hQKE D QE hQE a g fb v o π π' hk)
    (viewKeys2APm_card QE hqE QKE hqkE a g fb v)
  unfold IC.realPrPm IC.idealPrPm at h
  have e : pr (Blk × PCipher) (fun p => viewIC2APm Hb st r K D a g fb v
        (hiddenOutE (cf p.2) st.params (ivOfPre Hb (st1 st) a) (ba (deltaOf g)) p.1) p.2) =
      pr (Blk × PCipher) (fun p => viewIC2APm Hb st r K D a g fb v
        (@hiddenOut (icPrg (cf p.2)) st.params (ivOfPre Hb (st1 st) a) (ba (deltaOf g)) p.1)
          p.2) :=
    pr_congr fun p => by rw [hiddenOut_ic]
  rw [e] at h
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

end IC2APm

/-! ## The end-to-end statement, the continuation reading the tables after step 1 -/

section Main2APm

variable (Hb : Hashes) (st : Statement) (r : ByteArray) (K : Tab3 → Tab5F → PCipher → Cont2)

/-- **Two-phase zero knowledge with AES as random permutations and a continuation that reads the
tables after step 1** (`zk2_rom_ic_h23A` with permutation rows). The bound is

    (q₃ + q_k3)·2⁻¹²⁸ + Pr[GrindBad]
      + 221·(4607 + (q_E + q_kE) + 4607)/(2¹²⁸ − (nHi + 1)) + switchEps + ((q₅ + q_k5) + 1)·2⁻¹²⁸. -/
theorem zk2_rom_ic_h23A_perm (hh : ∀ G3 G5 π, Hyp2 st r (K G3 G5 π)) (hHb : HashesWF Hb)
    (hp : SmallParams st.params)
    (QK3 : ByteArray × ByteArray → Tab3 → Tab5F → PCipher → Finset (Bytes 16))
    (hQK3 : ∀ o1 G3 G3' G5 π, (∀ k ∈ QK3 o1 G3 G5 π, G3 k = G3' k) →
      K G3' G5 π o1 = K G3 G5 π o1)
    {qk3 : ℕ} (hqk3 : ∀ o1 G3 G5 π, (QK3 o1 G3 G5 π).card ≤ qk3)
    (QK5 : ByteArray × ByteArray → Tab3 → Tab5F → PCipher → Finset (Bytes 37))
    (hQK5 : ∀ o1 G3 G5 G5' π, (∀ key ∈ QK5 o1 G3 G5 π, G5 key = G5' key) →
      K G3 G5' π o1 = K G3 G5 π o1)
    {qk5 : ℕ} (hqk5 : ∀ o1 G3 G5 π, (QK5 o1 G3 G5 π).card ≤ qk5)
    (QKE : ByteArray × ByteArray → Tab3 → Tab5F → PCipher → Finset Blk)
    (hQKE : ∀ o1 G3 G5 π π', (∀ key ∈ QKE o1 G3 G5 π, π key = π' key) →
      K G3 G5 π' o1 = K G3 G5 π o1)
    {qkE : ℕ} (hqkE : ∀ o1 G3 G5 π, (QKE o1 G3 G5 π).card ≤ qkE)
    (D : Out2 → Tab3 → Tab2G st.params → Tab5F → PCipher → Prop)
    (Q3 : Out2 → Tab3 → Tab2G st.params → Tab5F → PCipher → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G2 G5 π, (∀ k ∈ Q3 o G3 G2 G5 π, G3 k = G3' k) →
      (D o G3 G2 G5 π ↔ D o G3' G2 G5 π))
    {q3 : ℕ} (hq3 : ∀ o G3 G2 G5 π, (Q3 o G3 G2 G5 π).card ≤ q3)
    (Q5 : Out2 → Tab3 → Tab2G st.params → Tab5F → PCipher → Finset (Bytes 37))
    (hQ5 : ∀ o G3 G2 G5 G5' π, (∀ k ∈ Q5 o G3 G2 G5 π, G5 k = G5' k) →
      (D o G3 G2 G5 π ↔ D o G3 G2 G5' π))
    {q5 : ℕ} (hq5 : ∀ o G3 G2 G5 π, (Q5 o G3 G2 G5 π).card ≤ q5)
    (QE : Out2 → Tab3 → Tab2G st.params → Tab5F → PCipher → Finset Blk)
    (hQE : ∀ o G3 G2 G5 π π', (∀ k ∈ QE o G3 G2 G5 π, π k = π' k) →
      (D o G3 G2 G5 π ↔ D o G3 G2 G5 π'))
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 π, (QE o G3 G2 G5 π).card ≤ qE) :
    |pr (((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × PCipher) (fun c =>
        D (@realRun2 (icPrg (cf c.2)) (recH Hb (st1 st) r c.1.2.1 c.1.1.2 c.1.2.2) CrtGen.tables
          st r (K c.1.2.1 c.1.2.2 c.2) (ba c.1.1.1)) c.1.2.1 c.1.1.2 c.1.2.2 c.2) -
      pr ((SimCoins2 st.params × Vis2 st.params) × PCipher) (fun c =>
        D (@simRun2 (icPrg (cf c.2)) Hb st r.size (K c.1.2.1 c.1.2.2.2 c.2) c.1.1) c.1.2.1
          (@simTab2 (icPrg (cf c.2)) Hb CrtGen.tables st (K c.1.2.1 c.1.2.2.2 c.2) c.1.2.2.2
            (@simRun2 (icPrg (cf c.2)) Hb st r.size (K c.1.2.1 c.1.2.2.2 c.2) c.1.1)
              c.1.1.1.1.2.1 c.1.2.2.1)
          c.1.2.2.2 c.2)| ≤
      (q3 + qk3) / 2 ^ 128 + pr Grind (GrindBad CrtGen.tables) +
        (221 * (4607 + ((qE + qkE : ℕ) + 4607)) / ((2 ^ 128 - (nHi st.params + 1) : ℕ) : ℝ) +
          switchEps st.params) + ((q5 + qk5 : ℕ) + 1) / 2 ^ 128 := by
  have hA := abs_pr_prod_sub_le'
    (fun (c : ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × PCipher) =>
      D (@realRun2 (icPrg (cf c.2)) (recH Hb (st1 st) r c.1.2.1 c.1.1.2 c.1.2.2) CrtGen.tables st r
        (K c.1.2.1 c.1.2.2 c.2) (ba c.1.1.1)) c.1.2.1 c.1.1.2 c.1.2.2 c.2)
    (fun (c : ((((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × Fallback st.params) ×
        (Tab3 × Tab5F)) × PCipher) =>
      @Dp2 (icPrg (cf c.2)) Hb CrtGen.tables st (K c.1.2.1 c.1.2.2 c.2)
        (fun o G3 G2 G5 => D o G3 G2 G5 c.2)
        (@hyb3' (icPrg (cf c.2)) (recB Hb (st1 st) r c.1.2.1 c.1.2.2) CrtGen.tables st r
          (K c.1.2.1 c.1.2.2 c.2) ((c.1.1.1.1.2, c.1.1.1.2.2), c.1.1.2)
          (@hiddenOut (icPrg (cf c.2)) st.params (ivOfPre Hb (st1 st) c.1.1.1.1.2)
            (ba (deltaOf c.1.1.1.2.2)) c.1.1.1.1.1))
        c.1.1.1.2.2 (c.1.2.1, c.1.1.1.2.1, c.1.2.2))
    (fun π => @zk2_pre_h4A (icPrg (cf π)) Hb st r (fun G3 G5 => K G3 G5 π) hHb
      (fun G3 G5 => hh G3 G5 π)
      (fun o1 G3 G5 => QK3 o1 G3 G5 π) (fun o1 G3 G3' G5 => hQK3 o1 G3 G3' G5 π) qk3
      (fun o1 G3 G5 => hqk3 o1 G3 G5 π)
      (fun o G3 G2 G5 => D o G3 G2 G5 π)
      (fun o G3 G2 G5 => Q3 o G3 G2 G5 π) (fun o G3 G3' G2 G5 => hQ3 o G3 G3' G2 G5 π) q3
      (fun o G3 G2 G5 => hq3 o G3 G2 G5 π))
  have hB := joint3_h4_2A_perm Hb st r K hp hh QKE hQKE hqkE D QE hQE hqE
  have hC := abs_pr_prod_sub_le'
    (fun (c : ((Hidden st.params × ((Bytes 16 × Grind) × Fallback st.params)) × Vis2 st.params) ×
        PCipher) =>
      @Dp2 (icPrg (cf c.2)) Hb CrtGen.tables st (K c.1.2.1 c.1.2.2.2 c.2)
        (fun o G3 G2 G5 => D o G3 G2 G5 c.2)
        (@hyb3' (icPrg (cf c.2)) (recB Hb (st1 st) r c.1.2.1 c.1.2.2.2) CrtGen.tables st r
          (K c.1.2.1 c.1.2.2.2 c.2) c.1.1.2 (hiddenIdeal (ba (deltaOf c.1.1.2.1.2)) c.1.1.1))
        c.1.1.2.1.2 c.1.2)
    (fun (c : (SimCoins2 st.params × Vis2 st.params) × PCipher) =>
      D (@simRun2 (icPrg (cf c.2)) Hb st r.size (K c.1.2.1 c.1.2.2.2 c.2) c.1.1) c.1.2.1
        (@simTab2 (icPrg (cf c.2)) Hb CrtGen.tables st (K c.1.2.1 c.1.2.2.2 c.2) c.1.2.2.2
          (@simRun2 (icPrg (cf c.2)) Hb st r.size (K c.1.2.1 c.1.2.2.2 c.2) c.1.1) c.1.1.1.1.2.1
            c.1.2.2.1) c.1.2.2.2 c.2)
    (fun π => @zk2_post_h4A (icPrg (cf π)) Hb st r (fun G3 G5 => K G3 G5 π) hHb
      (fun G3 G5 => hh G3 G5 π)
      (fun o1 G3 G5 => QK5 o1 G3 G5 π) (fun o1 G3 G5 G5' => hQK5 o1 G3 G5 G5' π) qk5
      (fun o1 G3 G5 => hqk5 o1 G3 G5 π)
      (fun o G3 G2 G5 => D o G3 G2 G5 π)
      (fun o G3 G2 G5 => Q5 o G3 G2 G5 π) (fun o G3 G2 G5 G5' => hQ5 o G3 G2 G5 G5' π) q5
      (fun o G3 G2 G5 => hq5 o G3 G2 G5 π))
  refine (abs_sub_le _ _ _).trans ((add_le_add hA ((abs_sub_le _ _ _).trans
    (add_le_add hB hC))).trans (le_of_eq (by push_cast; ring)))

/-- **`zk2_rom_ic_h23A_perm` with `Pr[GrindBad] ≤ 2⁻¹¹⁰`**: the error is
`εROPm p (q₃ + q_k3) (q₅ + q_k5) (q_E + q_kE)`. -/
theorem zk2_rom_ic_h23A_num_perm (hh : ∀ G3 G5 π, Hyp2 st r (K G3 G5 π)) (hHb : HashesWF Hb)
    (hp : SmallParams st.params)
    (QK3 : ByteArray × ByteArray → Tab3 → Tab5F → PCipher → Finset (Bytes 16))
    (hQK3 : ∀ o1 G3 G3' G5 π, (∀ k ∈ QK3 o1 G3 G5 π, G3 k = G3' k) →
      K G3' G5 π o1 = K G3 G5 π o1)
    {qk3 : ℕ} (hqk3 : ∀ o1 G3 G5 π, (QK3 o1 G3 G5 π).card ≤ qk3)
    (QK5 : ByteArray × ByteArray → Tab3 → Tab5F → PCipher → Finset (Bytes 37))
    (hQK5 : ∀ o1 G3 G5 G5' π, (∀ key ∈ QK5 o1 G3 G5 π, G5 key = G5' key) →
      K G3 G5' π o1 = K G3 G5 π o1)
    {qk5 : ℕ} (hqk5 : ∀ o1 G3 G5 π, (QK5 o1 G3 G5 π).card ≤ qk5)
    (QKE : ByteArray × ByteArray → Tab3 → Tab5F → PCipher → Finset Blk)
    (hQKE : ∀ o1 G3 G5 π π', (∀ key ∈ QKE o1 G3 G5 π, π key = π' key) →
      K G3 G5 π' o1 = K G3 G5 π o1)
    {qkE : ℕ} (hqkE : ∀ o1 G3 G5 π, (QKE o1 G3 G5 π).card ≤ qkE)
    (D : Out2 → Tab3 → Tab2G st.params → Tab5F → PCipher → Prop)
    (Q3 : Out2 → Tab3 → Tab2G st.params → Tab5F → PCipher → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G2 G5 π, (∀ k ∈ Q3 o G3 G2 G5 π, G3 k = G3' k) →
      (D o G3 G2 G5 π ↔ D o G3' G2 G5 π))
    {q3 : ℕ} (hq3 : ∀ o G3 G2 G5 π, (Q3 o G3 G2 G5 π).card ≤ q3)
    (Q5 : Out2 → Tab3 → Tab2G st.params → Tab5F → PCipher → Finset (Bytes 37))
    (hQ5 : ∀ o G3 G2 G5 G5' π, (∀ k ∈ Q5 o G3 G2 G5 π, G5 k = G5' k) →
      (D o G3 G2 G5 π ↔ D o G3 G2 G5' π))
    {q5 : ℕ} (hq5 : ∀ o G3 G2 G5 π, (Q5 o G3 G2 G5 π).card ≤ q5)
    (QE : Out2 → Tab3 → Tab2G st.params → Tab5F → PCipher → Finset Blk)
    (hQE : ∀ o G3 G2 G5 π π', (∀ k ∈ QE o G3 G2 G5 π, π k = π' k) →
      (D o G3 G2 G5 π ↔ D o G3 G2 G5 π'))
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 π, (QE o G3 G2 G5 π).card ≤ qE) :
    |pr (((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × PCipher) (fun c =>
        D (@realRun2 (icPrg (cf c.2)) (recH Hb (st1 st) r c.1.2.1 c.1.1.2 c.1.2.2) CrtGen.tables
          st r (K c.1.2.1 c.1.2.2 c.2) (ba c.1.1.1)) c.1.2.1 c.1.1.2 c.1.2.2 c.2) -
      pr ((SimCoins2 st.params × Vis2 st.params) × PCipher) (fun c =>
        D (@simRun2 (icPrg (cf c.2)) Hb st r.size (K c.1.2.1 c.1.2.2.2 c.2) c.1.1) c.1.2.1
          (@simTab2 (icPrg (cf c.2)) Hb CrtGen.tables st (K c.1.2.1 c.1.2.2.2 c.2) c.1.2.2.2
            (@simRun2 (icPrg (cf c.2)) Hb st r.size (K c.1.2.1 c.1.2.2.2 c.2) c.1.1)
              c.1.1.1.1.2.1 c.1.2.2.1)
          c.1.2.2.2 c.2)| ≤
      εROPm st.params (q3 + qk3) (q5 + qk5) (qE + qkE) := by
  refine (zk2_rom_ic_h23A_perm Hb st r K hh hHb hp QK3 hQK3 hqk3 QK5 hQK5 hqk5 QKE hQKE hqkE D Q3
    hQ3 hq3 Q5 hQ5 hq5 QE hQE hqE).trans ?_
  have := grindBad_le_110
  unfold εROPm
  push_cast
  linarith

end Main2APm

/-! ## In the games' form, and the instances -/

section Games

variable (Hb : Hashes) (st : Statement) (r : ByteArray) (n : ℕ)

/-- **Two-phase zero knowledge with AES as random permutations, with the tables visible**
(`zk2_ro` with permutation rows): error `εROPm p q₃ (q₅ + qk5) (q_E + qkE)`. -/
theorem zk2_ro_perm (K : ShPm st.params → Cont2) {qk5 qkE : ℕ} (hh : Hyp2RO st r n K qk5 qkE)
    (hHb : HashesWF Hb) (hp : SmallParams st.params) {q3 q5 qE : ℕ}
    (D : Out2 → Tab3 → ShPm st.params → Prop) (hD : Budget st.params q3 q5 qE D) :
    |pr ((Bytes 16 × Tab3) × ShPm st.params) (fun a =>
        D (realRO2 Hb st r K a.1.1 a.1.2 a.2) a.1.2 a.2) -
      pr ((SimCoins2 st.params × Tab3) × ShPm st.params) (fun a =>
        D (simRO2 Hb st n K a.1.1 a.2) a.1.2 (progRO2 Hb st n K a.1.1 a.2))| ≤
      εROPm st.params q3 (q5 + qk5) (qE + qkE) := by
  choose Q3 hQ3c hQ3 using hD.h3
  choose Q5 hQ5c hQ5 using hD.h5
  choose QE hQEc hQE using hD.hE
  obtain ⟨K', hKf⟩ : ∃ K' : Tab5F → PCipher → Cont2, K = fun s => K' s.2.1 s.2.2 :=
    ⟨fun G5 π => K (fun _ => 0, G5, π), funext fun s => (hh.h2 s fun _ => 0).symm⟩
  subst hKf
  obtain ⟨QK5, hQK5c, hQK5⟩ := hh.h5
  obtain ⟨QKE, hQKEc, hQKE⟩ := hh.hE
  have hr : r.size = n := hh.size
  subst hr
  have key := zk2_rom_ic_h23_num_perm Hb st r K' (fun G5 π => hh.hyp (fun _ => 0, G5, π)) hHb hp
    (fun G5 π => QK5 (fun _ => 0, G5, π))
    (fun G5 G5' π hk => (hQK5 (fun _ => 0, G5, π) G5' hk).symm)
    (fun G5 π => hQK5c _)
    (fun G5 π => QKE (fun _ => 0, G5, π))
    (fun G5 π π' hk => (hQKE (fun _ => 0, G5, π) π' hk).symm)
    (fun G5 π => hQKEc _)
    (fun o G3 G2 G5 π => D o G3 (G2, G5, π))
    (fun o G3 G2 G5 π => Q3 o (G2, G5, π) G3)
    (fun o G3 G3' G2 G5 π hk => Iff.of_eq (hQ3 o (G2, G5, π) G3 G3' hk).symm)
    (fun o G3 G2 G5 π => hQ3c o (G2, G5, π) G3)
    (fun o G3 G2 G5 π => Q5 o G3 (G2, G5, π))
    (fun o G3 G2 G5 G5' π hk => Iff.of_eq (hQ5 o G3 (G2, G5, π) G5' hk).symm)
    (fun o G3 G2 G5 π => hQ5c o G3 (G2, G5, π))
    (fun o G3 G2 G5 π => QE o G3 (G2, G5, π))
    (fun o G3 G2 G5 π π' hk => Iff.of_eq (hQE o G3 (G2, G5, π) π' hk).symm)
    (fun o G3 G2 G5 π => hQEc o G3 (G2, G5, π))
  let e1 : ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × PCipher ≃
      (Bytes 16 × Tab3) × ShPm st.params :=
    { toFun := fun c => ((c.1.1.1, c.1.2.1), (c.1.1.2, c.1.2.2, c.2))
      invFun := fun c => (((c.1.1, c.2.1), (c.1.2, c.2.2.1)), c.2.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e2 : (SimCoins2 st.params × Vis2 st.params) × PCipher ≃
      (SimCoins2 st.params × Tab3) × ShPm st.params :=
    { toFun := fun c => ((c.1.1, c.1.2.1), (c.1.2.2.1, c.1.2.2.2, c.2))
      invFun := fun c => ((c.1.1, (c.1.2, c.2.1, c.2.2.1)), c.2.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e1, ← pr_equiv e2]
  exact key

/-- **Two-phase zero knowledge with AES as random permutations, the continuation reading the
tables after step 1** (`zk2_adaptive` with permutation rows): error
`εROPm p (q₃ + qk3) (q₅ + qk5) (q_E + qkE)`. -/
theorem zk2_adaptive_perm (K : Tab3 → ShPm st.params → Cont2) {qk3 qk5 qkE : ℕ}
    (hh : Hyp2RA st r n K qk3 qk5 qkE) (hHb : HashesWF Hb) (hp : SmallParams st.params)
    {q3 q5 qE : ℕ} (D : Out2 → Tab3 → ShPm st.params → Prop) (hD : Budget st.params q3 q5 qE D) :
    |pr ((Bytes 16 × Tab3) × ShPm st.params) (fun a =>
        D (realRO2 Hb st r (K a.1.2) a.1.1 a.1.2 a.2) a.1.2 a.2) -
      pr ((SimCoins2 st.params × Tab3) × ShPm st.params) (fun a =>
        D (simRO2 Hb st n (K a.1.2) a.1.1 a.2) a.1.2 (progRO2 Hb st n (K a.1.2) a.1.1 a.2))| ≤
      εROPm st.params (q3 + qk3) (q5 + qk5) (qE + qkE) := by
  choose Q3 hQ3c hQ3 using hD.h3
  choose Q5 hQ5c hQ5 using hD.h5
  choose QE hQEc hQE using hD.hE
  obtain ⟨K', hKf⟩ : ∃ K' : Tab3 → Tab5F → PCipher → Cont2, K = fun g s => K' g s.2.1 s.2.2 :=
    ⟨fun g G5 π => K g (fun _ => 0, G5, π),
      funext fun g => funext fun s => (hh.h2 g s fun _ => 0).symm⟩
  subst hKf
  choose QK3 hQK3c hQK3 using hh.h3
  choose QK5 hQK5c hQK5 using hh.h5
  choose QKE hQKEc hQKE using hh.hE
  have hr : r.size = n := hh.size
  subst hr
  have key := zk2_rom_ic_h23A_num_perm Hb st r K' (fun G3 G5 π => hh.hyp G3 (fun _ => 0, G5, π))
    hHb hp
    (fun o1 G3 G5 π => QK3 o1 (fun _ => 0, G5, π) G3)
    (fun o1 G3 G3' G5 π hk => hQK3 o1 (fun _ => 0, G5, π) G3 G3' hk)
    (fun o1 G3 G5 π => hQK3c o1 _ G3)
    (fun o1 G3 G5 π => QK5 o1 G3 (fun _ => 0, G5, π))
    (fun o1 G3 G5 G5' π hk => hQK5 o1 G3 (fun _ => 0, G5, π) G5' hk)
    (fun o1 G3 G5 π => hQK5c o1 G3 _)
    (fun o1 G3 G5 π => QKE o1 G3 (fun _ => 0, G5, π))
    (fun o1 G3 G5 π π' hk => hQKE o1 G3 (fun _ => 0, G5, π) π' hk)
    (fun o1 G3 G5 π => hQKEc o1 G3 _)
    (fun o G3 G2 G5 π => D o G3 (G2, G5, π))
    (fun o G3 G2 G5 π => Q3 o (G2, G5, π) G3)
    (fun o G3 G3' G2 G5 π hk => Iff.of_eq (hQ3 o (G2, G5, π) G3 G3' hk).symm)
    (fun o G3 G2 G5 π => hQ3c o (G2, G5, π) G3)
    (fun o G3 G2 G5 π => Q5 o G3 (G2, G5, π))
    (fun o G3 G2 G5 G5' π hk => Iff.of_eq (hQ5 o G3 (G2, G5, π) G5' hk).symm)
    (fun o G3 G2 G5 π => hQ5c o G3 (G2, G5, π))
    (fun o G3 G2 G5 π => QE o G3 (G2, G5, π))
    (fun o G3 G2 G5 π π' hk => Iff.of_eq (hQE o G3 (G2, G5, π) π' hk).symm)
    (fun o G3 G2 G5 π => hQEc o G3 (G2, G5, π))
  let e1 : ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × PCipher ≃
      (Bytes 16 × Tab3) × ShPm st.params :=
    { toFun := fun c => ((c.1.1.1, c.1.2.1), (c.1.1.2, c.1.2.2, c.2))
      invFun := fun c => (((c.1.1, c.2.1), (c.1.2, c.2.2.1)), c.2.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e2 : (SimCoins2 st.params × Vis2 st.params) × PCipher ≃
      (SimCoins2 st.params × Tab3) × ShPm st.params :=
    { toFun := fun c => ((c.1.1, c.1.2.1), (c.1.2.2.1, c.1.2.2.2, c.2))
      invFun := fun c => ((c.1.1, (c.1.2, c.2.1, c.2.2.1)), c.2.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e1, ← pr_equiv e2]
  exact key

end Games

/-- **Permutation rows have `ZK2Row`** (`zk2_ro_perm`). -/
noncomputable instance ZK2Row.perm : ZK2Row (Equiv.Perm Blk) where
  zk2 Hb st r n K _ _ hh hHb hp _ _ _ D hD := zk2_ro_perm Hb st r n K hh hHb hp D hD

/-- **Permutation rows have `ZK2ARow`** (`zk2_adaptive_perm`). -/
noncomputable instance ZK2ARow.perm : ZK2ARow (Equiv.Perm Blk) where
  zk2A Hb st r n K _ _ _ hh hHb hp _ _ _ D hD := zk2_adaptive_perm Hb st r n K hh hHb hp D hD

end VoleMole.ZK.Sim
