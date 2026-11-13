import VoleMole.ZK.IdealCipherPermP
import VoleMole.ZK.ReadsROPerm
import VoleMole.ZK.AdaptRO

/-!
# Zero knowledge with patched tables and AES as uniformly random permutations

`zk_rom_ic_h23P` (`ZK/HopsPatch.lean`) runs the zero-knowledge chain with the `H₅` table patched
on a fixed set `P5` and the cipher table (of functions) on `PE`, for the statements an adversary
chooses after reading the tables (`ZK/AdaptRO.lean`). Here the cipher is a table of uniform
**permutations**, patched on `PE` (`IC.patchT PE WE π`: fixed permutations there, uniform ones
elsewhere), read by the distinguisher as whole permutations.

* **H4 with the permutation table patched** (`hide_puncture_permP`, `exper_finalPmP`,
  `hide_rom_query_permP`, from `IC.puncturePmP`): a hidden node's value must also avoid `PE`; each
  of the `221` hops costs `(4607 + q + |PE|)/(2¹²⁸ − (nHi + 1))`, and the switching term
  `switchEps` is unchanged (the replacement permutations are fresh).
* **The chain** (`joint3_h4P_perm`, `zk_rom_ic_h23P_perm`): the hops before and after H4 hold for
  every cipher (`zk_pre_h4Φ`, `zk_post_h4P` at `icPrg (cf (patchT PE WE π))`, the `H₅`-patch's H6
  term as in `zk_rom_ic_h23P`).
* **`zk_roP_perm`** (`εROPmP p q₃ q₅ q_E |P5| |PE|`) and the instance **`ZKPRow.perm`**: the
  adaptive-statement theorems and the games with a table-reading adversary hold with permutation
  rows.

    εROPmP p q₃ q₅ q_E n₅ n_E = q₃·2⁻¹²⁸ + 2⁻¹¹³ + 221·(4607 + q_E + 4607 + n_E)/(2¹²⁸ − (nHi + 1))
                                 + switchEps p + (q₅ + 1)·2⁻¹²⁸ + (n₅ + 1)·2⁻¹²⁸.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

set_option linter.unusedSectionVars false

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy
  VoleMole.ZK.IC

/-! ## H4 with the permutation table patched -/

section H4PPm

variable [HasPrg] (p : Params) (iv delta : ByteArray)

/-- **GGM puncturing with permutation rows, the table patched on `P`** (`hide_puncture_perm`,
`IC.puncturePmP`). -/
theorem hide_puncture_permP (hp : SmallParams p) (A : Hidden p → PCipher → Prop)
    (Q : Hidden p → PCipher → Finset Blk)
    (hQ : ∀ o G G', (∀ k ∈ Q o G, G k = G' k) → (A o G ↔ A o G')) {q : ℕ}
    (hq : ∀ o G, (Q o G).card ≤ q) (P : Finset Blk) (W : PCipher) :
    |experPmP (xIn iv) nN ∅ (hidOfRows p iv delta) A P W -
        experPmP (xIn iv) nN (hidSet delta) (hidOfRows p iv delta) A P W| ≤
      (hidSet delta).card * ((nN + q + P.card : ℕ) / ((2 ^ 128 - (nHi p + 1) : ℕ) : ℝ)) := by
  have h := puncturePmP (x := xIn iv) (N := nN) (fun n => hid delta n = true)
    (fun n hn hs h0 => hid_parent delta (by omega) hn hs) (rdH p iv) (rdH_card p iv)
    (nHi_succ_lt p hp) (fun n hn _ h0 => xIn_not_mem_rdH p iv hn h0)
    (fun n _ _ h0 m hm hmn hpm => xIn_mem_rdH p iv h0 hm hmn hpm) (hidOfRows p iv delta)
    (fun n hn hs h0 ρ ρ' hoff hon => hidOfRows_rd p iv delta hn h0 hs ρ ρ' hoff hon)
    (hidOfRows_congr p iv delta) A Q hQ hq P W
  rw [card_blk] at h
  exact h

/-- **The fully punctured experiment with the patched permutation table is `switchEps`-close to
the ideal one** (`exper_finalPm`). -/
theorem exper_finalPmP (hp : SmallParams p) (A : Hidden p → PCipher → Prop) (P : Finset Blk)
    (W : PCipher) :
    |experPmP (xIn iv) nN (hidSet delta) (hidOfRows p iv delta) A P W -
      pr (Hidden p × PCipher) (fun h => A (hiddenIdeal (p := p) delta h.1) (patchT P W h.2))| ≤
      switchEps p := by
  refine experPmP_close _ _ _ (fun π => ?_) A P W
  have h1 : Close (switchEps p) (fun R : Fin nN → Equiv.Perm Blk => finalF p iv delta (cf π)
      (partsEquiv p delta (restr p iv delta (cf R)))) (finalF p iv delta (cf π)) :=
    (((restr_closePm p iv delta hp).map fun a => finalF p iv delta (cf π) (partsEquiv p delta a)).trans
      (close_equiv (partsEquiv p delta) (finalF p iv delta (cf π)))).mono (by norm_num)
  have h2 := (close_prod_snd (α := Blk) (X := fun R : Fin nN → Equiv.Perm Blk =>
    finalF p iv delta (cf π) (partsEquiv p delta (restr p iv delta (cf R))))).trans h1
  have h3 := h2.trans (final_close p iv delta hp (cf π))
  have hfun : (fun c : PCoins Blk nN =>
      hidOfRows p iv delta (rowAt (xIn iv) nN (hidSet delta) (cf π) (cf c.2) c.1)) =
      fun x : Blk × (Fin nN → Equiv.Perm Blk) =>
        finalF p iv delta (cf π) (partsEquiv p delta (restr p iv delta (cf x.2))) :=
    funext fun c => hidOfRows_eq_finalF p iv delta hp (cf π) (cf c.2) c.1
  rw [hfun]
  exact h3.mono (by norm_num)

/-- **H4 with AES as random permutations and the table patched on `P`**: the hidden part from a
uniform root seed with the rows of the patched table, against the ideal hidden part, for a
distinguisher that sees the patched table and reads it at `q` keys (whole permutations):

    221·(4607 + q + |P|)/(2¹²⁸ − (nHi + 1)) + switchEps p. -/
theorem hide_rom_query_permP (hp : SmallParams p) (A : Hidden p → PCipher → Prop)
    (Q : Hidden p → PCipher → Finset Blk)
    (hQ : ∀ o G G', (∀ k ∈ Q o G, G k = G' k) → (A o G ↔ A o G')) {q : ℕ}
    (hq : ∀ o G, (Q o G).card ≤ q) (P : Finset Blk) (W : PCipher) :
    |pr (Blk × PCipher) (fun s => A (hiddenOutE (cf (patchT P W s.2)) p iv delta s.1)
        (patchT P W s.2)) -
      pr (Hidden p × PCipher) (fun h => A (hiddenIdeal (p := p) delta h.1) (patchT P W h.2))| ≤
      221 * (4607 + q + P.card) / ((2 ^ 128 - (nHi p + 1) : ℕ) : ℝ) + switchEps p := by
  have h := hide_puncture_permP p iv delta hp A Q hQ hq P W
  rw [experPmP_empty] at h
  have h2 := exper_finalPmP p iv delta hp A P W
  have hc : ((hidSet delta).card : ℝ) ≤ 221 := by exact_mod_cast hidSet_card delta
  have hn : ((nN + q + P.card : ℕ) : ℝ) = 4607 + q + P.card := by push_cast; rfl
  have hpos : (0 : ℝ) ≤ ((nN + q + P.card : ℕ) : ℝ) / ((2 ^ 128 - (nHi p + 1) : ℕ) : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have h3 : ((hidSet delta).card : ℝ) *
      (((nN + q + P.card : ℕ) : ℝ) / ((2 ^ 128 - (nHi p + 1) : ℕ) : ℝ)) ≤
      221 * (4607 + q + P.card) / ((2 ^ 128 - (nHi p + 1) : ℕ) : ℝ) := by
    rw [mul_div_assoc, ← hn]
    exact mul_le_mul_of_nonneg_right hc hpos
  exact (abs_sub_le _ _ _).trans (add_le_add (h.trans h3) h2)

end H4PPm

/-! ## The chain with both tables patched -/

section ICPPm

variable (Hb : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)

/-- **H4 with AES as random permutations, the permutation table patched on `PE`** (and the `H₅`
table any function `φ` of a uniform one; `joint3_h4P`):
`221·(4607 + q_E + 4607 + |PE|)/(2¹²⁸ − (nHi + 1)) + switchEps`. -/
theorem joint3_h4P_perm (hp : SmallParams st.params) {cs : ByteArray → ByteArray → System GF128}
    (hzk : ZKHyp T st w cs)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → PCipher → Prop)
    (QE : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → PCipher → Finset Blk)
    (hQE : ∀ o G3 G2 G5 π π', (∀ k ∈ QE o G3 G2 G5 π, π k = π' k) →
      (D o G3 G2 G5 π ↔ D o G3 G2 G5 π'))
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 π, (QE o G3 G2 G5 π).card ≤ qE) (φ : Tab5F → Tab5F)
    (PE : Finset Blk) (WE : PCipher) :
    |pr ((((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5F)) × PCipher)
        (fun c => @Dp (icPrg (cf (patchT PE WE c.2))) Hb T st
          (fun o G3 G2 G5 => D o G3 G2 G5 (patchT PE WE c.2))
          (@hyb3 (icPrg (cf (patchT PE WE c.2))) (recB Hb st w c.1.2.1 (φ c.1.2.2)) T st w
            (c.1.1.1.2, c.1.1.2.2)
            (@hiddenOut (icPrg (cf (patchT PE WE c.2))) st.params (ivOfPre Hb st c.1.1.1.2)
              (ba (deltaOf c.1.1.2.2)) c.1.1.1.1))
          c.1.1.2.2 (c.1.2.1, c.1.1.2.1, φ c.1.2.2)) -
      pr (((Hidden st.params × (Bytes 16 × Grind)) × Vis2 st.params) × PCipher) (fun c =>
        @Dp (icPrg (cf (patchT PE WE c.2))) Hb T st
          (fun o G3 G2 G5 => D o G3 G2 G5 (patchT PE WE c.2))
          (@hyb3 (icPrg (cf (patchT PE WE c.2))) (recB Hb st w c.1.2.1 (φ c.1.2.2.2)) T st w
            c.1.1.2 (hiddenIdeal (ba (deltaOf c.1.1.2.2)) c.1.1.1)) c.1.1.2.2 (vφ φ c.1.2))| ≤
      221 * (4607 + (qE + 4607) + PE.card) / ((2 ^ 128 - (nHi st.params + 1) : ℕ) : ℝ) +
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
  have h := hide_rom_query_permP st.params (ivOfPre Hb st a) (ba (deltaOf g)) hp
    (viewICPm Hb T st w D a g (vφ φ v)) (viewKeysPm Hb T st w QE a g (vφ φ v))
    (fun o π π' hk => viewICPm_congr hzk D QE hQE a g (vφ φ v) o π π' hk)
    (viewKeysPm_card QE hqE a g (vφ φ v)) PE WE
  have e : pr (Blk × PCipher) (fun p => viewICPm Hb T st w D a g (vφ φ v)
        (hiddenOutE (cf (patchT PE WE p.2)) st.params (ivOfPre Hb st a) (ba (deltaOf g)) p.1)
        (patchT PE WE p.2)) =
      pr (Blk × PCipher) (fun p => viewICPm Hb T st w D a g (vφ φ v)
        (@hiddenOut (icPrg (cf (patchT PE WE p.2))) st.params (ivOfPre Hb st a) (ba (deltaOf g))
          p.1) (patchT PE WE p.2)) :=
    pr_congr fun p => by rw [hiddenOut_ic]
  rw [e] at h
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

/-- **Zero knowledge with AES as random permutations, the `H₅` table patched on `P5` and the
permutation table on `PE`** (`zk_rom_ic_h23P` with permutation rows): the prover, the simulator's
recomputation and the distinguisher see `patchT P5 W5 G5` and `patchT PE WE π` for uniform `G5`,
`π`. The error is `zk_rom_ic_h23_perm`'s with `|PE|` added to each hop's candidates, plus
`(|P5| + 1)·2⁻¹²⁸`. -/
theorem zk_rom_ic_h23P_perm {cs : ByteArray → ByteArray → System GF128}
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
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 π, (QE o G3 G2 G5 π).card ≤ qE)
    (P5 : Finset (Bytes 37)) (W5 : Tab5F) (PE : Finset Blk) (WE : PCipher) :
    |pr (((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × PCipher) (fun c =>
        D (@Prover.prove (icPrg (cf (patchT PE WE c.2)))
          (recH Hb st w c.1.2.1 c.1.1.2 (patchT P5 W5 c.1.2.2)) CrtGen.tables st w
          (ba c.1.1.1) st.params.witnessBytes) c.1.2.1 c.1.1.2 (patchT P5 W5 c.1.2.2)
          (patchT PE WE c.2)) -
      pr ((SimCoins st.params × Vis2 st.params) × PCipher) (fun c =>
        D (simulate st.params c.1.1) c.1.2.1
          (@simTab (icPrg (cf (patchT PE WE c.2))) Hb CrtGen.tables st (patchT P5 W5 c.1.2.2.2)
            (simulate st.params c.1.1) c.1.1.1.2.1 c.1.2.2.1) (patchT P5 W5 c.1.2.2.2)
          (patchT PE WE c.2))| ≤
      q3 / 2 ^ 128 + pr Grind (GrindBad CrtGen.tables) +
        (221 * (4607 + (qE + 4607) + PE.card) / ((2 ^ 128 - (nHi st.params + 1) : ℕ) : ℝ) +
          switchEps st.params) +
        ((q5 + 1) / 2 ^ 128 + (P5.card + 1) / 2 ^ 128) := by
  have hA := abs_pr_prod_sub_le'
    (fun (c : ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × PCipher) =>
      D (@Prover.prove (icPrg (cf (patchT PE WE c.2)))
        (recH Hb st w c.1.2.1 c.1.1.2 (patchT P5 W5 c.1.2.2)) CrtGen.tables st w (ba c.1.1.1)
        st.params.witnessBytes) c.1.2.1 c.1.1.2 (patchT P5 W5 c.1.2.2) (patchT PE WE c.2))
    (fun (c : (((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5F)) × PCipher) =>
      @Dp (icPrg (cf (patchT PE WE c.2))) Hb CrtGen.tables st
        (fun o G3 G2 G5 => D o G3 G2 G5 (patchT PE WE c.2))
        (@hyb3 (icPrg (cf (patchT PE WE c.2))) (recB Hb st w c.1.2.1 (patchT P5 W5 c.1.2.2))
          CrtGen.tables st w (c.1.1.1.2, c.1.1.2.2)
          (@hiddenOut (icPrg (cf (patchT PE WE c.2))) st.params (ivOfPre Hb st c.1.1.1.2)
            (ba (deltaOf c.1.1.2.2)) c.1.1.1.1))
        c.1.1.2.2 (c.1.2.1, c.1.1.2.1, patchT P5 W5 c.1.2.2))
    (fun π => @zk_pre_h4Φ (icPrg (cf (patchT PE WE π))) Hb st w (patchT P5 W5) cs hlr hzk hHb
      (fun o G3 G2 G5 => D o G3 G2 G5 (patchT PE WE π))
      (fun o G3 G2 G5 => Q3 o G3 G2 G5 (patchT PE WE π))
      (fun o G3 G3' G2 G5 => hQ3 o G3 G3' G2 G5 (patchT PE WE π)) q3
      (fun o G3 G2 G5 => hq3 o G3 G2 G5 (patchT PE WE π)))
  have hB := joint3_h4P_perm Hb CrtGen.tables st w hp hzk D QE hQE hqE (patchT P5 W5) PE WE
  have hC := abs_pr_prod_sub_le'
    (fun (c : ((Hidden st.params × (Bytes 16 × Grind)) × Vis2 st.params) × PCipher) =>
      @Dp (icPrg (cf (patchT PE WE c.2))) Hb CrtGen.tables st
        (fun o G3 G2 G5 => D o G3 G2 G5 (patchT PE WE c.2))
        (@hyb3 (icPrg (cf (patchT PE WE c.2))) (recB Hb st w c.1.2.1 (patchT P5 W5 c.1.2.2.2))
          CrtGen.tables st w c.1.1.2 (hiddenIdeal (ba (deltaOf c.1.1.2.2)) c.1.1.1)) c.1.1.2.2
        (vφ (patchT P5 W5) c.1.2))
    (fun (c : (SimCoins st.params × Vis2 st.params) × PCipher) =>
      D (simulate st.params c.1.1) c.1.2.1
        (@simTab (icPrg (cf (patchT PE WE c.2))) Hb CrtGen.tables st (patchT P5 W5 c.1.2.2.2)
          (simulate st.params c.1.1) c.1.1.1.2.1 c.1.2.2.1) (patchT P5 W5 c.1.2.2.2)
        (patchT PE WE c.2))
    (fun π => @zk_post_h4P (icPrg (cf (patchT PE WE π))) Hb st w cs hlr hzk hHb
      (fun o G3 G2 G5 => D o G3 G2 G5 (patchT PE WE π))
      (fun o G3 G2 G5 => Q5 o G3 G2 G5 (patchT PE WE π))
      (fun o G3 G2 G5 G5' => hQ5 o G3 G2 G5 G5' (patchT PE WE π)) q5
      (fun o G3 G2 G5 => hq5 o G3 G2 G5 (patchT PE WE π)) P5 W5)
  refine (abs_sub_le _ _ _).trans ((add_le_add hA ((abs_sub_le _ _ _).trans
    (add_le_add hB hC))).trans (le_of_eq (by ring)))

end ICPPm

/-! ## In the games' form, and the instance -/

section ZKPPm

/-- **The error of `zk_roP_perm`**: `εROPm` with `|PE|` added to the hops' candidates, plus the
`H₅` patch's `(|P5| + 1)·2⁻¹²⁸`. -/
noncomputable def εROPmP (p : Params) (q3 q5 qE n5 nE : ℕ) : ℝ :=
  q3 / 2 ^ 128 + 1 / 2 ^ 113 +
    (221 * (4607 + (qE + 4607) + nE) / ((2 ^ 128 - (nHi p + 1) : ℕ) : ℝ) + switchEps p) +
      ((q5 + 1) / 2 ^ 128 + (n5 + 1) / 2 ^ 128)

lemma εROPmP_nonneg (p : Params) (q3 q5 qE n5 nE : ℕ) : 0 ≤ εROPmP p q3 q5 qE n5 nE := by
  unfold εROPmP switchEps; positivity

lemma εROPmP_mono (p : Params) {q3 q5 qE n5 nE q3' q5' qE' n5' nE' : ℕ} (h3 : q3 ≤ q3')
    (h5 : q5 ≤ q5') (hE : qE ≤ qE') (h5' : n5 ≤ n5') (hE' : nE ≤ nE') :
    εROPmP p q3 q5 qE n5 nE ≤ εROPmP p q3' q5' qE' n5' nE' := by
  unfold εROPmP
  have a3 : (q3 : ℝ) ≤ q3' := by exact_mod_cast h3
  have a5 : (q5 : ℝ) ≤ q5' := by exact_mod_cast h5
  have aE : (qE : ℝ) ≤ qE' := by exact_mod_cast hE
  have b5 : (n5 : ℝ) ≤ n5' := by exact_mod_cast h5'
  have bE : (nE : ℝ) ≤ nE' := by exact_mod_cast hE'
  gcongr

variable (Hb : Hashes) (st : Statement) (w : ByteArray)

/-- **Zero knowledge with AES as random permutations, with `H₅` patched on `P5` and the
permutation table on `PE`** (`zk_roP` with permutation rows): the prover, the simulator's
programming and the distinguisher see the patched tables; error `εROPmP`. -/
theorem zk_roP_perm {cs : ByteArray → ByteArray → System GF128} (hlr : st.params.labelRows = true)
    (hzk : ZKHyp CrtGen.tables st w cs) (hHb : HashesWF Hb) (hp : SmallParams st.params)
    {q3 q5 qE : ℕ} (D : Except String ByteArray → Tab3 → ShPm st.params → Prop)
    (hD : Budget st.params q3 q5 qE D) (P5 : Finset (Bytes 37)) (W5 : Tab5F) (PE : Finset Blk)
    (WE : PCipher) :
    |pr ((Bytes 16 × Tab3) × ShPm st.params) (fun a =>
        D (realRO st.params Hb st w a.1.1 a.1.2 (patch5E P5 W5 PE WE a.2)) a.1.2
          (patch5E P5 W5 PE WE a.2)) -
      pr ((SimCoins st.params × Tab3) × ShPm st.params) (fun a =>
        D (simulate st.params a.1.1) a.1.2
          (progRO st.params Hb st a.1.1 (patch5E P5 W5 PE WE a.2)))| ≤
      εROPmP st.params q3 q5 qE P5.card PE.card := by
  choose Q3 hQ3c hQ3 using hD.h3
  choose Q5 hQ5c hQ5 using hD.h5
  choose QE hQEc hQE using hD.hE
  have key := zk_rom_ic_h23P_perm Hb st w hlr hzk hHb hp (fun o G3 G2 G5 π => D o G3 (G2, G5, π))
    (fun o G3 G2 G5 π => Q3 o (G2, G5, π) G3)
    (fun o G3 G3' G2 G5 π hk => Iff.of_eq (hQ3 o (G2, G5, π) G3 G3' hk).symm)
    (fun o G3 G2 G5 π => hQ3c o (G2, G5, π) G3)
    (fun o G3 G2 G5 π => Q5 o G3 (G2, G5, π))
    (fun o G3 G2 G5 G5' π hk => Iff.of_eq (hQ5 o G3 (G2, G5, π) G5' hk).symm)
    (fun o G3 G2 G5 π => hQ5c o G3 (G2, G5, π))
    (fun o G3 G2 G5 π => QE o G3 (G2, G5, π))
    (fun o G3 G2 G5 π π' hk => Iff.of_eq (hQE o G3 (G2, G5, π) π' hk).symm)
    (fun o G3 G2 G5 π => hQEc o G3 (G2, G5, π)) P5 W5 PE WE
  let e1 : ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × PCipher ≃
      (Bytes 16 × Tab3) × ShPm st.params :=
    { toFun := fun c => ((c.1.1.1, c.1.2.1), (c.1.1.2, c.1.2.2, c.2))
      invFun := fun c => (((c.1.1, c.2.1), (c.1.2, c.2.2.1)), c.2.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e2 : (SimCoins st.params × Vis2 st.params) × PCipher ≃
      (SimCoins st.params × Tab3) × ShPm st.params :=
    { toFun := fun c => ((c.1.1, c.1.2.1), (c.1.2.2.1, c.1.2.2.2, c.2))
      invFun := fun c => ((c.1.1, (c.1.2, c.2.1, c.2.2.1)), c.2.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e1, ← pr_equiv e2]
  refine key.trans ?_
  have := grindBad_le_113
  unfold εROPmP
  linarith

/-- **Permutation rows have `ZKPRow`** (`zk_roP_perm`, error `εROPmP`). -/
noncomputable instance ZKPRow.perm : ZKPRow (Equiv.Perm Blk) where
  εP := εROPmP
  εP_nonneg := εROPmP_nonneg
  εP_mono p _ _ _ _ _ _ _ _ _ _ h3 h5 hE h5' hE' := εROPmP_mono p h3 h5 hE h5' hE'
  zkP Hb st w _ hlr hzk hHb hp _ _ _ D hD P5 W5 PE WE :=
    zk_roP_perm Hb st w hlr hzk hHb hp D hD P5 W5 PE WE

/-- **The `H₂³` term with AES as random permutations** (`h23G` at permutation rows). -/
noncomputable def h23Pm (p : Params) (d n5 nE n2 : ℕ) : ℝ :=
  if n2 = 0 then 0 else
    1 / 2 ^ 113 + εROPmP p 0 312 4607 n5 nE + 2 * (noHitProb + n2 / 2 ^ (8 * (16 * (d - 1))))

/-- **The error of `zk_adaptive` with AES as random permutations** (`εAdG` at permutation rows):
`εROPmP p q₃ q₅ q_E s₅ s_E + s₃·2⁻¹²⁸ + h23Pm p d s₅ s_E s₂`. -/
noncomputable def εAdPm (p : Params) (d q3 q5 qE s3 s2 s5 sE : ℕ) : ℝ :=
  εROPmP p q3 q5 qE s5 sE + s3 / 2 ^ 128 + h23Pm p d s5 sE s2

lemma εAdG_perm (p : Params) : εAdG (Equiv.Perm Blk) p = εAdPm p := rfl

end ZKPPm

end VoleMole.ZK.Sim
