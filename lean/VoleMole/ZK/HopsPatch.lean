import VoleMole.ZK.HopsIC
import VoleMole.ZK.GrindNum
import VoleMole.ZK.IdealCipherP

/-!
# The zero-knowledge chain with the `H₅` and cipher tables patched on fixed key sets

`zk_rom_ic_h23` (`ZK/HopsIC.lean`) is for uniform tables. An adversary that reads the tables
**before** the statement is fixed (`ZK/AdaptRO.lean`) conditions them on the answers it saw: given
its view, the tables are uniform except on its query sets, where they are fixed. Here the chain is
run with the `H₅` table patched on a fixed set `P5` and the cipher table patched on a fixed set
`PE` (`IC.patchT`: fixed values there, the uniform table elsewhere), the prover, the simulator's
recomputation and the distinguisher all reading the patched tables.

* **The hops that do not use a table's uniformity hold for every value of it**, so they hold for
  the patched table: H1, grinding and programming, the programmed points recomputed (before H4;
  `zk_pre_h4Φ`, with `H₅` any function `φ` of the uniform table), the tape and the simulator (after
  H4); all of them for every cipher table.
* **H6 with the `H₅` table patched** (`lab_rom_query_sGP`, `joint2_h6P`): the sibling answers read
  off the patched table are the unpatched ones unless a sibling input is in `P5`, which is a guess
  of the uniform label-row pad `Θ` per key of `P5` (`pr_bad_leG`): `≤ (|P5| + 1)·2⁻¹²⁸` more.
* **H4 with the cipher patched** (`hide_rom_queryP`, `joint3_h4P`): the GGM puncturing of
  `IC.punctureP`, where a hidden node's value must also avoid `PE`: the `221` hops cost
  `(4607 + q + |PE|)·2⁻¹²⁸` each.

**`zk_rom_ic_h23P`**: the error of `zk_rom_ic_h23` plus `221·|PE|·2⁻¹²⁸ + (|P5| + 1)·2⁻¹²⁸`.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy
open VoleMole.ZK.IC (patchT patchT_of_mem patchT_of_not_mem)

set_option linter.unusedSectionVars false

/-! ## H6 with the `H₅` table patched -/

section H6P

variable [HasPrg] (Hs : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)
  (cs : ByteArray → ByteArray → System GF128)
  {K : Type} [Fintype K] [DecidableEq K] (enc : K → ByteArray)
  (sk : Shared × PadsU st.params → Fin 312 → K)

/-- **A sibling input is read with probability `≤ (q + 1)·2⁻¹²⁸`** (`pr_bad_leG`), for a query set
that sees the prover's output on the patched table. -/
theorem pr_sib_badP
    (hsk : ∀ c e, enc (sk c e) = sibInput Hs T st c.1 (withSib c.2 fun _ => fun _ => 0) e)
    (hlr : st.params.labelRows = true) (h : ZKHyp T st w cs)
    (QQ : Except String ByteArray → Shared → (K → Bytes 4) → Finset K)
    {q : ℕ} (hq : ∀ o s G, (QQ o s G).card ≤ q) (P : Finset K) (W : K → Bytes 4) :
    pr ((Shared × PadsU st.params) × ((K → Bytes 4) × Sib)) (fun x => ∃ e, sk x.1 e ∈
      proverKeysG Hs T st enc (x.1.1, withSib x.1.2 x.2.2) ∪
        QQ (proveIdeal (Hs.withTable .h5 enc (patchT P W x.2.1 : K → Bytes 4)) T st w (x.1.1, withSib x.1.2 x.2.2))
          x.1.1 (patchT P W x.2.1)) ≤ (q + 1) / 2 ^ 128 := by
  let E : (K → Bytes 4) × IdealTape st.params ≃
      (Shared × PadsU st.params) × ((K → Bytes 4) × Sib) :=
    { toFun := fun y => ((y.2.1, dropSib y.2.2), (y.1, y.2.2.2.2.2.2.2.2))
      invFun := fun x => (x.2.1, (x.1.1, withSib x.1.2 x.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv E]
  refine pr_prod_le _ fun G => pr_prod_le _ fun s => ?_
  exact pr_bad_leG Hs T st w cs enc sk (fun o G => QQ o s G) hsk hlr h (fun o G => hq o s G)
    (patchT P W G) s

/-- **H6's query bound with the `H₅` table patched on `P`** (`lab_rom_query_sG` for the prover, the
sibling answers and the distinguisher on `patchT P W G`): `+ (|P| + 1)·2⁻¹²⁸`. -/
theorem lab_rom_query_sGP
    (hsk : ∀ c e, enc (sk c e) = sibInput Hs T st c.1 (withSib c.2 fun _ => fun _ => 0) e)
    (hkey : ∀ c e, keyOf enc (sk c e) = sk c e)
    (hlr : st.params.labelRows = true) (h : ZKHyp T st w cs)
    (D : Except String ByteArray → Shared → (K → Bytes 4) → Prop)
    (QD : Except String ByteArray → Shared → (K → Bytes 4) → Finset K)
    (hA : ∀ (t : IdealTape st.params) G G', (∀ k ∈ proverKeysG Hs T st enc t ∪
        QD (proveIdeal (Hs.withTable .h5 enc G) T st w t) t.1 G, G k = G' k) →
      (D (proveIdeal (Hs.withTable .h5 enc G) T st w t) t.1 G ↔
        D (proveIdeal (Hs.withTable .h5 enc G') T st w t) t.1 G'))
    {q : ℕ} (hq : ∀ o s G, (QD o s G).card ≤ q) (P : Finset K) (W : K → Bytes 4) :
    |pr ((Shared × PadsU st.params) × (K → Bytes 4)) (fun x =>
        D (proveIdeal (Hs.withTable .h5 enc (patchT P W x.2 : K → Bytes 4)) T st w
          (fillSib (Hs.withTable .h5 enc (patchT P W x.2 : K → Bytes 4)) T st
            (x.1.1, withSib x.1.2 fun _ => fun _ => 0))) x.1.1 (patchT P W x.2)) -
      pr ((Shared × PadsU st.params) × ((K → Bytes 4) × Sib))
        (fun x => D (proveIdeal (Hs.withTable .h5 enc (patchT P W x.2.1 : K → Bytes 4)) T st w
          (x.1.1, withSib x.1.2 x.2.2)) x.1.1 (patchT P W x.2.1))| ≤
      (q + 1) / 2 ^ 128 + (P.card + 1) / 2 ^ 128 := by
  let A : IdealTape st.params → (K → Bytes 4) → Prop := fun t G =>
    D (proveIdeal (Hs.withTable .h5 enc (patchT P W G : K → Bytes 4)) T st w t) t.1 (patchT P W G)
  let Q : IdealTape st.params → (K → Bytes 4) → Finset K := fun t G =>
    proverKeysG Hs T st enc t ∪
      QD (proveIdeal (Hs.withTable .h5 enc (patchT P W G : K → Bytes 4)) T st w t) t.1 (patchT P W G)
  have hQ : ∀ t G G', (∀ k ∈ Q t G, G k = G' k) → (A t G ↔ A t G') := by
    intro t G G' hG
    refine hA t _ _ fun k hk => ?_
    by_cases hkP : k ∈ P
    · simp only [patchT, hkP, ↓reduceIte]; rfl
    · simp only [patchT, hkP, ↓reduceIte]; exact hG k hk
  have hlab := lab_romG Hs T st enc sk hsk hkey A Q hQ
  have hswap : |pr ((Shared × PadsU st.params) × (K → Bytes 4)) (fun x =>
        D (proveIdeal (Hs.withTable .h5 enc (patchT P W x.2 : K → Bytes 4)) T st w
          (fillSib (Hs.withTable .h5 enc (patchT P W x.2 : K → Bytes 4)) T st
            (x.1.1, withSib x.1.2 fun _ => fun _ => 0))) x.1.1 (patchT P W x.2)) -
      pr ((Shared × PadsU st.params) × (K → Bytes 4)) (fun x =>
        A (fillSib (Hs.withTable .h5 enc x.2) T st (x.1.1, withSib x.1.2 fun _ => fun _ => 0)) x.2)| ≤
      pr ((Shared × PadsU st.params) × (K → Bytes 4)) (fun x => ∃ e, sk x.1 e ∈ P) := by
    refine abs_pr_sub_le_of_agree _ _ _ fun x hx => ?_
    push Not at hx
    have e1 := fillSib_withTableG Hs T st enc sk hsk hkey (patchT P W x.2) x.1 (fun _ => fun _ => 0)
    have e2 := fillSib_withTableG Hs T st enc sk hsk hkey x.2 x.1 (fun _ => fun _ => 0)
    have e3 : patchT P W x.2 ∘ sk x.1 = x.2 ∘ sk x.1 :=
      funext fun e => patchT_of_not_mem _ _ (hx e)
    show D _ _ _ ↔ D _ _ _
    rw [e1, e2, e3]
  have hb1 : pr ((Shared × PadsU st.params) × (K → Bytes 4)) (fun x => ∃ e, sk x.1 e ∈ P) ≤
      (P.card + 1) / 2 ^ 128 := by
    rw [pr_prod_fst (β := K → Bytes 4) (fun c : Shared × PadsU st.params => ∃ e, sk c e ∈ P),
      ← pr_prod_fst (β := (K → Bytes 4) × Sib) (fun c : Shared × PadsU st.params => ∃ e, sk c e ∈ P)]
    refine (pr_mono fun x hx => ?_).trans (pr_sib_badP Hs T st w cs enc sk hsk hlr h
      (fun _ _ _ => P) (fun _ _ _ => le_rfl) P W)
    obtain ⟨e, he⟩ := hx
    exact ⟨e, Finset.mem_union_right _ he⟩
  have hb2 := pr_sib_badP Hs T st w cs enc sk hsk hlr h QD hq P W
  have := abs_sub_le (pr ((Shared × PadsU st.params) × (K → Bytes 4)) (fun x =>
        D (proveIdeal (Hs.withTable .h5 enc (patchT P W x.2 : K → Bytes 4)) T st w
          (fillSib (Hs.withTable .h5 enc (patchT P W x.2 : K → Bytes 4)) T st
            (x.1.1, withSib x.1.2 fun _ => fun _ => 0))) x.1.1 (patchT P W x.2)))
    (pr ((Shared × PadsU st.params) × (K → Bytes 4)) (fun x =>
        A (fillSib (Hs.withTable .h5 enc x.2) T st (x.1.1, withSib x.1.2 fun _ => fun _ => 0)) x.2))
    (pr ((Shared × PadsU st.params) × ((K → Bytes 4) × Sib))
        (fun x => D (proveIdeal (Hs.withTable .h5 enc (patchT P W x.2.1 : K → Bytes 4)) T st w
          (x.1.1, withSib x.1.2 x.2.2)) x.1.1 (patchT P W x.2.1)))
  have hlab' : |pr ((Shared × PadsU st.params) × (K → Bytes 4)) (fun x =>
        A (fillSib (Hs.withTable .h5 enc x.2) T st (x.1.1, withSib x.1.2 fun _ => fun _ => 0)) x.2) -
      pr ((Shared × PadsU st.params) × ((K → Bytes 4) × Sib))
        (fun x => D (proveIdeal (Hs.withTable .h5 enc (patchT P W x.2.1 : K → Bytes 4)) T st w
          (x.1.1, withSib x.1.2 x.2.2)) x.1.1 (patchT P W x.2.1))| ≤ (q + 1) / 2 ^ 128 :=
    hlab.trans hb2
  linarith

/-- **`lab_rom_hyp_sG` with the `H₅` table patched on `P`.** -/
theorem lab_rom_hyp_sGP
    (hsk : ∀ c e, enc (sk c e) = sibInput Hs T st c.1 (withSib c.2 fun _ => fun _ => 0) e)
    (hkey : ∀ c e, keyOf enc (sk c e) = sk c e)
    (hlr : st.params.labelRows = true) (h : ZKHyp T st w cs)
    (D : Except String ByteArray → Shared → (K → Bytes 4) → Prop)
    (QD : Except String ByteArray → Shared → (K → Bytes 4) → Finset K)
    (hA : ∀ (t : IdealTape st.params) G G', (∀ k ∈ proverKeysG Hs T st enc t ∪
        QD (proveIdeal (Hs.withTable .h5 enc G) T st w t) t.1 G, G k = G' k) →
      (D (proveIdeal (Hs.withTable .h5 enc G) T st w t) t.1 G ↔
        D (proveIdeal (Hs.withTable .h5 enc G') T st w t) t.1 G'))
    {q : ℕ} (hq : ∀ o s G, (QD o s G).card ≤ q) (P : Finset K) (W : K → Bytes 4) :
    |pr (IdealTape st.params × (K → Bytes 4)) (fun x =>
        D (proveIdeal (Hs.withTable .h5 enc (patchT P W x.2 : K → Bytes 4)) T st w
          (fillSib (Hs.withTable .h5 enc (patchT P W x.2 : K → Bytes 4)) T st x.1)) x.1.1 (patchT P W x.2)) -
      pr (IdealTape st.params × (K → Bytes 4))
        (fun x => D (proveIdeal (Hs.withTable .h5 enc (patchT P W x.2 : K → Bytes 4)) T st w x.1) x.1.1
          (patchT P W x.2))| ≤
      (q + 1) / 2 ^ 128 + (P.card + 1) / 2 ^ 128 := by
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
      D (proveIdeal (Hs.withTable .h5 enc (patchT P W x.2 : K → Bytes 4)) T st w
        (fillSib (Hs.withTable .h5 enc (patchT P W x.2 : K → Bytes 4)) T st x.1)) x.1.1 (patchT P W x.2)) =
      pr ((Shared × PadsU st.params) × (K → Bytes 4)) (fun x =>
        D (proveIdeal (Hs.withTable .h5 enc (patchT P W x.2 : K → Bytes 4)) T st w
          (fillSib (Hs.withTable .h5 enc (patchT P W x.2 : K → Bytes 4)) T st
          (x.1.1, withSib x.1.2 fun _ => fun _ => 0))) x.1.1 (patchT P W x.2)) := by
    rw [← pr_equiv E2, ← pr_prod_fst (β := Sib) (fun x : (Shared × PadsU st.params) ×
      (K → Bytes 4) => D (proveIdeal (Hs.withTable .h5 enc (patchT P W x.2 : K → Bytes 4)) T st w
        (fillSib (Hs.withTable .h5 enc (patchT P W x.2 : K → Bytes 4)) T st
          (x.1.1, withSib x.1.2 fun _ => fun _ => 0))) x.1.1 (patchT P W x.2))]
    refine pr_congr fun y => ?_
    show D (proveIdeal (Hs.withTable .h5 enc (patchT P W y.1.2 : K → Bytes 4)) T st w
        (fillSib (Hs.withTable .h5 enc (patchT P W y.1.2 : K → Bytes 4)) T st
        (y.1.1.1, withSib y.1.1.2 y.2))) y.1.1.1 (patchT P W y.1.2) ↔ _
    rw [fillSib_withSib T st _ y.1.1.1 y.1.1.2 y.2 fun _ => fun _ => 0]
  have e2 : pr (IdealTape st.params × (K → Bytes 4))
      (fun x => D (proveIdeal (Hs.withTable .h5 enc (patchT P W x.2 : K → Bytes 4)) T st w x.1) x.1.1
        (patchT P W x.2)) =
      pr ((Shared × PadsU st.params) × ((K → Bytes 4) × Sib))
        (fun x => D (proveIdeal (Hs.withTable .h5 enc (patchT P W x.2.1 : K → Bytes 4)) T st w
          (x.1.1, withSib x.1.2 x.2.2)) x.1.1 (patchT P W x.2.1)) :=
    (pr_equiv E3 _).symm
  rw [e1, e2]
  exact lab_rom_query_sGP Hs T st w cs enc sk hsk hkey hlr h D QD hA hq P W

end H6P

/-! ## H4 with the cipher table patched -/

section H4P

open VoleMole.ZK.IC

variable [HasPrg] (p : Params) (iv delta : ByteArray)

/-- **GGM puncturing with the cipher patched on `P`** (`hide_puncture`, `IC.punctureP`). -/
theorem hide_punctureP (A : Hidden p → Cipher → Prop) (Q : Hidden p → Cipher → Finset Blk)
    (hQ : ∀ o G G', (∀ k ∈ Q o G, G k = G' k) → (A o G ↔ A o G')) {q : ℕ}
    (hq : ∀ o G, (Q o G).card ≤ q) (P : Finset Blk) (W : Cipher) :
    |experP (xIn iv) nN ∅ (hidOfRows p iv delta) A P W -
        experP (xIn iv) nN (hidSet delta) (hidOfRows p iv delta) A P W| ≤
      (hidSet delta).card * ((nN + q + P.card : ℕ) / 2 ^ 128) := by
  have h := punctureP (x := xIn iv) (N := nN) (fun n => hid delta n = true)
    (fun n hn hs h0 => hid_parent delta (by omega) hn hs)
    (fun n _ _ h0 m hm hmn hp => xIn_sib iv hm h0 hmn hp) (hidOfRows p iv delta)
    (fun n hn hs h0 ρ y => hidOfRows_point p iv delta hn h0 hs ρ y)
    (hidOfRows_congr p iv delta) A Q hQ hq P W
  rw [card_blk] at h
  exact_mod_cast h

/-- For every cipher table, the fully punctured hidden part is the ideal one (`exper_final`). -/
theorem final_close_rows (hp : SmallParams p) (E : Cipher) :
    Close 0 (fun c : Coins Blk Blk nN => hidOfRows p iv delta (rowAt (xIn iv) nN (hidSet delta) E c.2 c.1))
      (hiddenIdeal (p := p) delta) := by
  have h1 : Close 0 (fun R : Fin nN → Blk → Blk => finalF p iv delta E
      (partsEquiv p delta (restr p iv delta R))) (finalF p iv delta E) :=
    (((restr_close p iv delta hp).map fun a => finalF p iv delta E (partsEquiv p delta a)).trans
      (close_equiv (partsEquiv p delta) (finalF p iv delta E))).mono (by norm_num)
  have h2 := (close_prod_snd (α := Blk) (X := fun R : Fin nN → Blk → Blk =>
    finalF p iv delta E (partsEquiv p delta (restr p iv delta R)))).trans h1
  have h3 := h2.trans (final_close p iv delta hp E)
  have h4 : Close 0 (fun x : Blk × (Fin nN → Blk → Blk) =>
      finalF p iv delta E (partsEquiv p delta (restr p iv delta x.2))) (hiddenIdeal (p := p) delta) :=
    fun D => (h3 D).trans (le_of_eq (by norm_num))
  have hfun : (fun c : Coins Blk Blk nN =>
      hidOfRows p iv delta (rowAt (xIn iv) nN (hidSet delta) E c.2 c.1)) =
      fun x : Blk × (Fin nN → Blk → Blk) =>
        finalF p iv delta E (partsEquiv p delta (restr p iv delta x.2)) :=
    funext fun c => hidOfRows_eq_finalF p iv delta hp E c.2 c.1
  rw [hfun]
  exact h4

/-- **H4 in the ideal-cipher model with the cipher patched on `P`** (`hide_rom_query`): the hidden
part from a uniform root seed with the patched table, against the ideal hidden part, for a
distinguisher that sees the patched table and reads it at `q` keys: `221·(4607 + q + |P|)·2⁻¹²⁸`. -/
theorem hide_rom_queryP (hp : SmallParams p) (A : Hidden p → Cipher → Prop)
    (Q : Hidden p → Cipher → Finset Blk)
    (hQ : ∀ o G G', (∀ k ∈ Q o G, G k = G' k) → (A o G ↔ A o G')) {q : ℕ}
    (hq : ∀ o G, (Q o G).card ≤ q) (P : Finset Blk) (W : Cipher) :
    |pr (Blk × Cipher) (fun s => A (hiddenOutE (patchT P W s.2) p iv delta s.1) (patchT P W s.2)) -
      pr (Hidden p × Cipher) (fun h => A (hiddenIdeal (p := p) delta h.1) (patchT P W h.2))| ≤
      221 * (4607 + q + P.card) / 2 ^ 128 := by
  have h := hide_punctureP p iv delta A Q hQ hq P W
  rw [experP_empty, experP_eq_of_close _ _ (hiddenIdeal (p := p) delta)
    (final_close_rows p iv delta hp) A P W] at h
  refine h.trans ?_
  have hc : ((hidSet delta).card : ℝ) ≤ 221 := by exact_mod_cast hidSet_card delta
  have hn : ((nN + q + P.card : ℕ) : ℝ) = 4607 + q + P.card := by push_cast; rfl
  rw [mul_div_assoc, hn]
  exact mul_le_mul_of_nonneg_right hc (by positivity)

end H4P

/-! ## The hops that hold for every value of the `H₅` table -/

section ChainΦ

variable [HasPrg] (Hb : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)

/-- The tables with the `H₅` table mapped by `φ`. -/
def vφ (φ : Tab5F → Tab5F) {p : Params} (v : Vis2 p) : Vis2 p := (v.1, v.2.1, φ v.2.2)

/-- **H1 for fixed `H₂³` and `H₅` tables** (the body of `joint2_h1`). -/
theorem joint2_h1_at (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Prop)
    (Q3 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G2 G5, (∀ k ∈ Q3 o G3 G2 G5, G3 k = G3' k) →
      (D o G3 G2 G5 ↔ D o G3' G2 G5))
    {q3 : ℕ} (hq3 : ∀ o G3 G2 G5, (Q3 o G3 G2 G5).card ≤ q3) (G2 : Tab2G st.params) (G5 : Tab5F) :
    |pr (Bytes 16 × Tab3) (fun b => D (proveP (recH Hb st w b.2 G2 G5) T st w
        (preR Hb T st w G5) b.1) b.2 G2 G5) -
      pr (Tab3 × (Bytes 16 × Bytes 16)) (fun b => D (runP (recH Hb st w b.1 G2 G5) T st w
        (preR Hb T st w G5) b.2) b.1 G2 G5)| ≤ q3 / 2 ^ 128 := by
  let wP := w.extract 0 st.params.witnessBytes
  let R : Bytes 16 × Bytes 16 → Except String ByteArray :=
    runP (recH Hb st w (fun _ => 0) G2 G5) T st w (preR Hb T st w G5)
  have hR : ∀ G3 : Tab3, runP (recH Hb st w G3 G2 G5) T st w (preR Hb T st w G5) = R :=
    fun G3 => by rw [runP_agreeOff_h3' (recH_agreeOff_h3 _ (fun _ => 0) G2 G5)]
  let A : Bytes 16 × Bytes 16 → Tab3 → Prop := fun v G3 => D (R v) G3 G2 G5
  have h := h3_rom_query (st.mu1 Hb) wP Hb A (fun v G3 => Q3 (R v) G3 G2 G5)
    (fun v G3 G3' hk => hQ3 (R v) G3 G3' G2 G5 hk) (fun v G3 => hq3 _ G3 G2 G5)
  have e1 : pr (Bytes 16 × Tab3) (fun b => D (proveP (recH Hb st w b.2 G2 G5) T st w
      (preR Hb T st w G5) b.1) b.2 G2 G5) = pr (Bytes 16 × (Bytes 16 → Bytes 32)) (fun p =>
        A (h3Seed (Hb.withTable .h3 (seedInput (st.mu1 Hb) wP) p.2) (st.mu1 Hb) wP (ba p.1)) p.2) := by
    refine pr_congr fun b => ?_
    simp only [A, proveP, recH_h3Seed, h3Seed_withTable, hR]
  have e2 : pr (Bytes 16 × ((Bytes 16 → Bytes 32) × Bytes 32)) (fun p => A (splitSeed p.2.2) p.2.1) =
      pr (Tab3 × (Bytes 16 × Bytes 16)) (fun b => D (runP (recH Hb st w b.1 G2 G5) T st w
        (preR Hb T st w G5) b.2) b.1 G2 G5) := by
    rw [pr_prod_snd (α := Bytes 16) (fun q : (Bytes 16 → Bytes 32) × Bytes 32 => A (splitSeed q.2) q.1),
      ← pr_equiv (Equiv.prodCongr (Equiv.refl Tab3) splitEquiv)]
    refine pr_congr fun b => ?_
    simp only [A, hR]
    rfl
  rw [e1, ← e2]
  exact h

/-- **H1 with the `H₅` table `φ` of a uniform one** (`joint2_h1`). -/
theorem joint2_h1Φ (φ : Tab5F → Tab5F)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Prop)
    (Q3 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G2 G5, (∀ k ∈ Q3 o G3 G2 G5, G3 k = G3' k) →
      (D o G3 G2 G5 ↔ D o G3' G2 G5))
    {q3 : ℕ} (hq3 : ∀ o G3 G2 G5, (Q3 o G3 G2 G5).card ≤ q3) :
    |pr ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) (fun c =>
        D (proveP (recH Hb st w c.2.1 c.1.2 (φ c.2.2)) T st w (preR Hb T st w (φ c.2.2)) c.1.1)
          c.2.1 c.1.2 (φ c.2.2)) -
      pr (((Bytes 16 × Bytes 16) × Tab2G st.params) × (Tab3 × Tab5F)) (fun c =>
        D (runP (recH Hb st w c.2.1 c.1.2 (φ c.2.2)) T st w (preR Hb T st w (φ c.2.2)) c.1.1)
          c.2.1 c.1.2 (φ c.2.2))| ≤ q3 / 2 ^ 128 := by
  let E0 : (Tab2G st.params × Tab5F) × (Bytes 16 × Tab3) ≃
      (Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F) :=
    { toFun := fun c => ((c.2.1, c.1.1), (c.2.2, c.1.2))
      invFun := fun c => ((c.1.2, c.2.2), (c.1.1, c.2.1))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let E1 : (Tab2G st.params × Tab5F) × (Tab3 × (Bytes 16 × Bytes 16)) ≃
      ((Bytes 16 × Bytes 16) × Tab2G st.params) × (Tab3 × Tab5F) :=
    { toFun := fun c => ((c.2.2, c.1.1), (c.2.1, c.1.2))
      invFun := fun c => ((c.1.2, c.2.2), (c.2.1, c.1.1))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv E0, ← pr_equiv E1]
  refine abs_pr_prod_sub_le _ _ fun a => ?_
  exact joint2_h1_at Hb T st w D Q3 hQ3 hq3 a.1 (φ a.2)

/-- **Grinding and programming for fixed `H₃` and `H₅` tables** (the body of `joint2_prog`). -/
theorem joint2_prog_at (hHb : HashesWF Hb) {cs : ByteArray → ByteArray → System GF128}
    (h : ZKHypQ st w cs)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Prop) (G3 : Tab3)
    (G5 : Tab5F) :
    |pr ((Bytes 16 × Bytes 16) × Tab2G st.params) (fun c =>
        D (runP (recH Hb st w G3 c.2 G5) T st w (preR Hb T st w G5) c.1) G3 c.2 G5) -
      pr ((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) (fun c =>
        D (hyb3 (recB Hb st w G3 G5) T st w (c.1.2, c.2.2)
          (hiddenOut st.params (ivOfPre Hb st c.1.2) (ba (deltaOf c.2.2)) c.1.1))
          G3 (programAt (key2 st.params (preR Hb T st w G5 c.1)) c.2.2 c.2.1) G5)| ≤ 0 := by
  rw [abs_nonpos_iff, sub_eq_zero]
  have e := pr_program_eq (C := Bytes 16 × Bytes 16) (R := Bytes 16)
    (x := fun c => key2 st.params (preR Hb T st w G5 c)) (fun c => key2_injective _ _)
    (fun c (u : Grind) (G2 : Tab2G st.params) => D (hyb3 (recB Hb st w G3 G5) T st w (c.2, u)
      (hiddenOut st.params (ivOfPre Hb st c.2) (ba (deltaOf u)) c.1)) G3 G2 G5)
  refine (pr_congr fun c => ?_).trans (e.trans (pr_congr fun c => Iff.rfl))
  rw [runP_recH Hb T st w hHb h]

/-- **Grinding and programming with the `H₅` table `φ` of a uniform one** (`joint2_prog`). -/
theorem joint2_progΦ (φ : Tab5F → Tab5F) (hHb : HashesWF Hb)
    {cs : ByteArray → ByteArray → System GF128} (h : ZKHypQ st w cs)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Prop) :
    |pr (((Bytes 16 × Bytes 16) × Tab2G st.params) × (Tab3 × Tab5F)) (fun c =>
        D (runP (recH Hb st w c.2.1 c.1.2 (φ c.2.2)) T st w (preR Hb T st w (φ c.2.2)) c.1.1)
          c.2.1 c.1.2 (φ c.2.2)) -
      pr (((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5F)) (fun c =>
        D (hyb3 (recB Hb st w c.2.1 (φ c.2.2)) T st w (c.1.1.2, c.1.2.2)
          (hiddenOut st.params (ivOfPre Hb st c.1.1.2) (ba (deltaOf c.1.2.2)) c.1.1.1))
          c.2.1 (programAt (key2 st.params (preR Hb T st w (φ c.2.2) c.1.1)) c.1.2.2 c.1.2.1)
          (φ c.2.2))| ≤ 0 :=
  abs_pr_prod_sub_le' _ _ fun v => joint2_prog_at Hb T st w hHb h D v.1 (φ v.2)

/-- **The programmed points recomputed, with the `H₅` table `φ` of a uniform one**
(`joint2_keys`; the argument is pointwise). -/
theorem joint2_keysΦ (φ : Tab5F → Tab5F) (hHb : HashesWF Hb)
    {cs : ByteArray → ByteArray → System GF128} (h : ZKHyp CrtGen.tables st w cs)
    (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Prop) :
    |pr (((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5F)) (fun c =>
        D (hyb3 (recB Hb st w c.2.1 (φ c.2.2)) CrtGen.tables st w (c.1.1.2, c.1.2.2)
          (hiddenOut st.params (ivOfPre Hb st c.1.1.2) (ba (deltaOf c.1.2.2)) c.1.1.1))
          c.2.1 (programAt (key2 st.params (preR Hb CrtGen.tables st w (φ c.2.2) c.1.1)) c.1.2.2
            c.1.2.1) (φ c.2.2)) -
      pr (((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5F)) (fun c =>
        Dp Hb CrtGen.tables st D (hyb3 (recB Hb st w c.2.1 (φ c.2.2)) CrtGen.tables st w
          (c.1.1.2, c.1.2.2)
          (hiddenOut st.params (ivOfPre Hb st c.1.1.2) (ba (deltaOf c.1.2.2)) c.1.1.1))
          c.1.2.2 (c.2.1, c.1.2.1, φ c.2.2))| ≤
      pr Grind (GrindBad CrtGen.tables) := by
  refine (abs_pr_sub_le_of_agree _ _ (fun c => GrindBad CrtGen.tables c.1.2.2) fun c hc => ?_).trans
    (le_of_eq ?_)
  · obtain ⟨⟨x, G2, g⟩, G3, G5₀⟩ := c
    dsimp only at hc ⊢
    generalize φ G5₀ = G5
    have hwf : HashesWF (recB Hb st w G3 G5) := recH_wf hHb G3 _ G5
    obtain ⟨proof, hok, hv⟩ := hyb3_vPre hwf h hlab x g hc
    have hiv : ivOfPre (recB Hb st w G3 G5) st = ivOfPre Hb st :=
      recH_ivOfPre G3 (fun _ => 0) G5
    have hvp : vPre (recB Hb st w G3 G5) CrtGen.tables st =
        vPre (rec5 Hb G5) CrtGen.tables st := vPre_recH G3 (fun _ => 0) G5
    have hpp : prePrefix (recB Hb st w G3 G5) CrtGen.tables st w =
        preR Hb CrtGen.tables st w G5 := prePrefix_recH G3 (fun _ => 0) G5
    rw [hiv] at hok
    rw [hvp, hpp] at hv
    simp only [Dp, simTab]
    rw [hok, outPre, hv]
  · rw [pr_prod_fst (β := Tab3 × Tab5F)
      (fun a : (Bytes 16 × Bytes 16) × (Tab2G st.params × Grind) => GrindBad CrtGen.tables a.2.2),
      pr_prod_snd (α := Bytes 16 × Bytes 16)
        (fun a : Tab2G st.params × Grind => GrindBad CrtGen.tables a.2),
      pr_prod_snd (α := Tab2G st.params) (GrindBad CrtGen.tables)]

/-- **The hybrids before H4 with the `H₅` table `φ` of a uniform one** (`zk_pre_h4`). -/
theorem zk_pre_h4Φ (φ : Tab5F → Tab5F) {cs : ByteArray → ByteArray → System GF128}
    (hlr : st.params.labelRows = true)
    (hzk : ZKHyp CrtGen.tables st w cs) (hHb : HashesWF Hb)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Prop)
    (Q3 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G2 G5, (∀ k ∈ Q3 o G3 G2 G5, G3 k = G3' k) →
      (D o G3 G2 G5 ↔ D o G3' G2 G5))
    {q3 : ℕ} (hq3 : ∀ o G3 G2 G5, (Q3 o G3 G2 G5).card ≤ q3) :
    |pr ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) (fun c =>
        D (Prover.prove (recH Hb st w c.2.1 c.1.2 (φ c.2.2)) CrtGen.tables st w (ba c.1.1))
          c.2.1 c.1.2 (φ c.2.2)) -
      pr (((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5F)) (fun c =>
        Dp Hb CrtGen.tables st D (hyb3 (recB Hb st w c.2.1 (φ c.2.2)) CrtGen.tables st w
          (c.1.1.2, c.1.2.2)
          (hiddenOut st.params (ivOfPre Hb st c.1.1.2) (ba (deltaOf c.1.2.2)) c.1.1.1))
          c.1.2.2 (c.2.1, c.1.2.1, φ c.2.2))| ≤
      q3 / 2 ^ 128 + pr Grind (GrindBad CrtGen.tables) := by
  obtain ⟨hl1, -, -, hl2⟩ := labelRows_sizes hlr
  have hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows := by omega
  have e0 : pr ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) (fun c =>
      D (Prover.prove (recH Hb st w c.2.1 c.1.2 (φ c.2.2)) CrtGen.tables st w (ba c.1.1))
        c.2.1 c.1.2 (φ c.2.2)) =
      pr ((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) (fun c =>
        D (proveP (recH Hb st w c.2.1 c.1.2 (φ c.2.2)) CrtGen.tables st w
          (preR Hb CrtGen.tables st w (φ c.2.2)) c.1.1) c.2.1 c.1.2 (φ c.2.2)) := by
    refine pr_congr fun c => ?_
    have hR : RunHyp (recH Hb st w c.2.1 c.1.2 (φ c.2.2)) CrtGen.tables st w cs :=
      ⟨hzk, recH_wf hHb _ _ _, bavcComplete, fun rho => crtComplete _ _ _ _ rho _ hlab, hlab⟩
    rw [← proveP_prove _ CrtGen.tables st w hR c.1.1, prePrefix_recH]
  rw [e0]
  have h1 := joint2_h1Φ Hb CrtGen.tables st w φ D Q3 hQ3 hq3
  have h2 := joint2_progΦ Hb CrtGen.tables st w φ hHb hzk.q D
  have h3 := joint2_keysΦ Hb st w φ hHb hzk hlab D
  have := abs_sub_le _ _ _ |>.trans (add_le_add h1 ((abs_sub_le _ _ _).trans (add_le_add h2 h3)))
  exact this.trans (le_of_eq (by ring))

/-- **The tape, for fixed tables** (the body of `joint2_tape`). -/
theorem joint2_tape_at (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Prop)
    (v : Vis2 st.params) :
    |pr (Hidden st.params × (Bytes 16 × Grind)) (fun c =>
        Dp Hb T st D (hyb3 (recB Hb st w v.1 v.2.2) T st w c.2
          (hiddenIdeal (ba (deltaOf c.2.2)) c.1)) c.2.2 v) -
      pr (IdealTape st.params) (fun c =>
        Dp Hb T st D (proveIdeal (recB Hb st w v.1 v.2.2) T st w
          (fillSib (recB Hb st w v.1 v.2.2) T st c)) c.1.2.1 v)| ≤ 0 := by
  rw [abs_nonpos_iff, sub_eq_zero]
  set R := recB Hb st w v.1 v.2.2
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

/-- **The tape with the `H₅` table `φ` of a uniform one** (`joint2_tape`). -/
theorem joint2_tapeΦ (φ : Tab5F → Tab5F)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Prop) :
    |pr ((Hidden st.params × (Bytes 16 × Grind)) × Vis2 st.params) (fun c =>
        Dp Hb T st D (hyb3 (recB Hb st w c.2.1 (φ c.2.2.2)) T st w c.1.2
          (hiddenIdeal (ba (deltaOf c.1.2.2)) c.1.1)) c.1.2.2 (vφ φ c.2)) -
      pr (IdealTape st.params × Vis2 st.params) (fun c =>
        Dp Hb T st D (proveIdeal (recB Hb st w c.2.1 (φ c.2.2.2)) T st w
          (fillSib (recB Hb st w c.2.1 (φ c.2.2.2)) T st c.1)) c.1.1.2.1 (vφ φ c.2))| ≤ 0 :=
  abs_pr_prod_sub_le' _ _ fun v => joint2_tape_at Hb T st w D (vφ φ v)

/-- **The simulator, for fixed tables** (`joint2_sim`). -/
theorem joint2_simΦ (φ : Tab5F → Tab5F) {cs : ByteArray → ByteArray → System GF128}
    (hzk : ZKHyp T st w cs)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Prop) :
    |pr (IdealTape st.params × Vis2 st.params) (fun c =>
        Dp Hb T st D (proveIdeal (recB Hb st w c.2.1 (φ c.2.2.2)) T st w c.1) c.1.1.2.1 (vφ φ c.2)) -
      pr (SimCoins st.params × Vis2 st.params) (fun c =>
        Dp Hb T st D (simulate st.params c.1) c.1.1.2.1 (vφ φ c.2))| ≤ 0 :=
  abs_pr_prod_sub_le' _ _ fun v => by
    have := proveIdeal_close_shared (recB Hb st w v.1 (φ v.2.2)) T st w cs hzk
      (fun os => Dp Hb T st D os.1 os.2.2.1 (vφ φ v))
    dsimp only at this ⊢
    exact this

/-- **H6 with the `H₅` table patched on `P5`** (`joint2_h6`, `lab_rom_hyp_sGP`):
`(q₅ + 1)·2⁻¹²⁸ + (|P5| + 1)·2⁻¹²⁸`. -/
theorem joint2_h6P {cs : ByteArray → ByteArray → System GF128} (hlr : st.params.labelRows = true)
    (hzk : ZKHyp T st w cs) (hHb : HashesWF Hb)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Prop)
    (Q5 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F →
      Finset (Bytes 37))
    (hQ5 : ∀ o G3 G2 G5 G5', (∀ k ∈ Q5 o G3 G2 G5, G5 k = G5' k) →
      (D o G3 G2 G5 ↔ D o G3 G2 G5'))
    {q5 : ℕ} (hq5 : ∀ o G3 G2 G5, (Q5 o G3 G2 G5).card ≤ q5) (P5 : Finset (Bytes 37))
    (W5 : Tab5F) :
    |pr (IdealTape st.params × Vis2 st.params) (fun c =>
        Dp Hb T st D (proveIdeal (recB Hb st w c.2.1 (patchT P5 W5 c.2.2.2)) T st w
          (fillSib (recB Hb st w c.2.1 (patchT P5 W5 c.2.2.2)) T st c.1)) c.1.1.2.1
          (vφ (patchT P5 W5) c.2)) -
      pr (IdealTape st.params × Vis2 st.params) (fun c =>
        Dp Hb T st D (proveIdeal (recB Hb st w c.2.1 (patchT P5 W5 c.2.2.2)) T st w c.1) c.1.1.2.1
          (vφ (patchT P5 W5) c.2))| ≤
      (q5 + 1) / 2 ^ 128 + (P5.card + 1) / 2 ^ 128 := by
  obtain ⟨h1, -, -, h2⟩ := labelRows_sizes hlr
  have hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows := by omega
  let E6 : (Tab3 × Tab2G st.params) × (IdealTape st.params × Tab5F) ≃
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
  exact lab_rom_hyp_sGP base T st w cs enc5 sk hsk hkey hlr hzk
    (fun o (s : Shared) G5 => Dp Hb T st D o s.2.1 (G3, G2, G5))
    (fun o (s : Shared) G5 => Q5 o G3 (simTab Hb T st G5 o s.2.1 G2) G5) hA
    (fun o s G => hq5 _ _ _ _) P5 W5

/-- **The hybrids after H4 with the `H₅` table patched on `P5`** (`zk_post_h4`). -/
theorem zk_post_h4P {cs : ByteArray → ByteArray → System GF128} (hlr : st.params.labelRows = true)
    (hzk : ZKHyp CrtGen.tables st w cs) (hHb : HashesWF Hb)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Prop)
    (Q5 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F →
      Finset (Bytes 37))
    (hQ5 : ∀ o G3 G2 G5 G5', (∀ k ∈ Q5 o G3 G2 G5, G5 k = G5' k) →
      (D o G3 G2 G5 ↔ D o G3 G2 G5'))
    {q5 : ℕ} (hq5 : ∀ o G3 G2 G5, (Q5 o G3 G2 G5).card ≤ q5) (P5 : Finset (Bytes 37))
    (W5 : Tab5F) :
    |pr ((Hidden st.params × (Bytes 16 × Grind)) × Vis2 st.params) (fun c =>
        Dp Hb CrtGen.tables st D (hyb3 (recB Hb st w c.2.1 (patchT P5 W5 c.2.2.2)) CrtGen.tables st w
          c.1.2 (hiddenIdeal (ba (deltaOf c.1.2.2)) c.1.1)) c.1.2.2 (vφ (patchT P5 W5) c.2)) -
      pr (SimCoins st.params × Vis2 st.params) (fun c =>
        D (simulate st.params c.1) c.2.1
          (simTab Hb CrtGen.tables st (patchT P5 W5 c.2.2.2) (simulate st.params c.1) c.1.1.2.1
            c.2.2.1) (patchT P5 W5 c.2.2.2))| ≤
      (q5 + 1) / 2 ^ 128 + (P5.card + 1) / 2 ^ 128 := by
  have h5 := joint2_tapeΦ Hb CrtGen.tables st w (patchT P5 W5) D
  have h6 := joint2_h6P Hb CrtGen.tables st w hlr hzk hHb D Q5 hQ5 hq5 P5 W5
  have h7 := joint2_simΦ Hb CrtGen.tables st w (patchT P5 W5) hzk D
  have := abs_sub_le _ _ _ |>.trans (add_le_add h5 ((abs_sub_le _ _ _).trans (add_le_add h6 h7)))
  exact this.trans (le_of_eq (by ring))

end ChainΦ

/-! ## H4 and the end-to-end statement with both tables patched -/

section ICP

variable (Hb : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)

/-- **H4 in the ideal-cipher model with the cipher patched on `PE`** (and the `H₅` table any
function `φ` of a uniform one; `joint3_h4`): `221·(4607 + q_E + 4607 + |PE|)·2⁻¹²⁸`. -/
theorem joint3_h4P (hp : SmallParams st.params) {cs : ByteArray → ByteArray → System GF128}
    (hzk : ZKHyp T st w cs)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Prop)
    (QE : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset Blk)
    (hQE : ∀ o G3 G2 G5 E E', (∀ k ∈ QE o G3 G2 G5 E, E k = E' k) →
      (D o G3 G2 G5 E ↔ D o G3 G2 G5 E'))
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 E, (QE o G3 G2 G5 E).card ≤ qE) (φ : Tab5F → Tab5F)
    (PE : Finset Blk) (WE : Cipher) :
    |pr ((((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5F)) × Cipher)
        (fun c => @Dp (icPrg (patchT PE WE c.2)) Hb T st
          (fun o G3 G2 G5 => D o G3 G2 G5 (patchT PE WE c.2))
          (@hyb3 (icPrg (patchT PE WE c.2)) (recB Hb st w c.1.2.1 (φ c.1.2.2)) T st w
            (c.1.1.1.2, c.1.1.2.2)
            (@hiddenOut (icPrg (patchT PE WE c.2)) st.params (ivOfPre Hb st c.1.1.1.2)
              (ba (deltaOf c.1.1.2.2)) c.1.1.1.1))
          c.1.1.2.2 (c.1.2.1, c.1.1.2.1, φ c.1.2.2)) -
      pr (((Hidden st.params × (Bytes 16 × Grind)) × Vis2 st.params) × Cipher) (fun c =>
        @Dp (icPrg (patchT PE WE c.2)) Hb T st (fun o G3 G2 G5 => D o G3 G2 G5 (patchT PE WE c.2))
          (@hyb3 (icPrg (patchT PE WE c.2)) (recB Hb st w c.1.2.1 (φ c.1.2.2.2)) T st w c.1.1.2
            (hiddenIdeal (ba (deltaOf c.1.1.2.2)) c.1.1.1)) c.1.1.2.2 (vφ φ c.1.2))| ≤
      221 * (4607 + (qE + 4607) + PE.card) / 2 ^ 128 := by
  let E2 : ((Bytes 16 × Grind) × Vis2 st.params) × (Blk × Cipher) ≃
      (((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5F)) × Cipher :=
    { toFun := fun c => ((((c.2.1, c.1.1.1), (c.1.2.2.1, c.1.1.2)), (c.1.2.1, c.1.2.2.2)), c.2.2)
      invFun := fun c => (((c.1.1.1.2, c.1.1.2.2), (c.1.2.1, c.1.1.2.1, c.1.2.2)), (c.1.1.1.1, c.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let E3 : ((Bytes 16 × Grind) × Vis2 st.params) × (Hidden st.params × Cipher) ≃
      ((Hidden st.params × (Bytes 16 × Grind)) × Vis2 st.params) × Cipher :=
    { toFun := fun c => (((c.2.1, c.1.1), c.1.2), c.2.2)
      invFun := fun c => ((c.1.1.2, c.1.2), (c.1.1.1, c.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv E2, ← pr_equiv E3]
  refine abs_pr_prod_sub_le _ _ fun x => ?_
  obtain ⟨⟨a, g⟩, v⟩ := x
  have h := hide_rom_queryP st.params (ivOfPre Hb st a) (ba (deltaOf g)) hp
    (viewIC Hb T st w D a g (vφ φ v)) (viewKeys Hb T st w QE a g (vφ φ v))
    (fun o E E' hk => viewIC_congr hzk D QE hQE a g (vφ φ v) o E E' hk)
    (viewKeys_card QE hqE a g (vφ φ v)) PE WE
  have e : pr (Blk × Cipher) (fun p => viewIC Hb T st w D a g (vφ φ v)
        (hiddenOutE (patchT PE WE p.2) st.params (ivOfPre Hb st a) (ba (deltaOf g)) p.1)
        (patchT PE WE p.2)) =
      pr (Blk × Cipher) (fun p => viewIC Hb T st w D a g (vφ φ v)
        (@hiddenOut (icPrg (patchT PE WE p.2)) st.params (ivOfPre Hb st a) (ba (deltaOf g)) p.1)
        (patchT PE WE p.2)) :=
    pr_congr fun p => by rw [hiddenOut_ic]
  rw [e] at h
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

/-- **Zero knowledge in the random-oracle and ideal-cipher model, with the `H₅` table patched on
`P5` and the cipher on `PE`** (`zk_rom_ic_h23`): the prover, the simulator's recomputation and the
distinguisher see `patchT P5 W5 G5` and `patchT PE WE E` for uniform `G5`, `E`. The error is
`zk_rom_ic_h23`'s plus `221·|PE|·2⁻¹²⁸ + (|P5| + 1)·2⁻¹²⁸`. -/
theorem zk_rom_ic_h23P {cs : ByteArray → ByteArray → System GF128} (hlr : st.params.labelRows = true)
    (hzk : ZKHyp CrtGen.tables st w cs) (hHb : HashesWF Hb) (hp : SmallParams st.params)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Prop)
    (Q3 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G2 G5 E, (∀ k ∈ Q3 o G3 G2 G5 E, G3 k = G3' k) →
      (D o G3 G2 G5 E ↔ D o G3' G2 G5 E))
    {q3 : ℕ} (hq3 : ∀ o G3 G2 G5 E, (Q3 o G3 G2 G5 E).card ≤ q3)
    (Q5 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset (Bytes 37))
    (hQ5 : ∀ o G3 G2 G5 G5' E, (∀ k ∈ Q5 o G3 G2 G5 E, G5 k = G5' k) →
      (D o G3 G2 G5 E ↔ D o G3 G2 G5' E))
    {q5 : ℕ} (hq5 : ∀ o G3 G2 G5 E, (Q5 o G3 G2 G5 E).card ≤ q5)
    (QE : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset Blk)
    (hQE : ∀ o G3 G2 G5 E E', (∀ k ∈ QE o G3 G2 G5 E, E k = E' k) →
      (D o G3 G2 G5 E ↔ D o G3 G2 G5 E'))
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 E, (QE o G3 G2 G5 E).card ≤ qE)
    (P5 : Finset (Bytes 37)) (W5 : Tab5F) (PE : Finset Blk) (WE : Cipher) :
    |pr (((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × Cipher) (fun c =>
        D (@Prover.prove (icPrg (patchT PE WE c.2))
          (recH Hb st w c.1.2.1 c.1.1.2 (patchT P5 W5 c.1.2.2)) CrtGen.tables st w
          (ba c.1.1.1) st.params.witnessBytes) c.1.2.1 c.1.1.2 (patchT P5 W5 c.1.2.2)
          (patchT PE WE c.2)) -
      pr ((SimCoins st.params × Vis2 st.params) × Cipher) (fun c =>
        D (simulate st.params c.1.1) c.1.2.1
          (@simTab (icPrg (patchT PE WE c.2)) Hb CrtGen.tables st (patchT P5 W5 c.1.2.2.2)
            (simulate st.params c.1.1) c.1.1.1.2.1 c.1.2.2.1) (patchT P5 W5 c.1.2.2.2)
          (patchT PE WE c.2))| ≤
      q3 / 2 ^ 128 + pr Grind (GrindBad CrtGen.tables) +
        221 * (4607 + (qE + 4607) + PE.card) / 2 ^ 128 +
        ((q5 + 1) / 2 ^ 128 + (P5.card + 1) / 2 ^ 128) := by
  have hA := abs_pr_avgE
    (fun (c : (Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) (E : Cipher) =>
      D (@Prover.prove (icPrg (patchT PE WE E)) (recH Hb st w c.2.1 c.1.2 (patchT P5 W5 c.2.2))
        CrtGen.tables st w (ba c.1.1) st.params.witnessBytes) c.2.1 c.1.2 (patchT P5 W5 c.2.2)
        (patchT PE WE E))
    (fun (c : ((Bytes 16 × Bytes 16) × (Tab2G st.params × Grind)) × (Tab3 × Tab5F)) (E : Cipher) =>
      @Dp (icPrg (patchT PE WE E)) Hb CrtGen.tables st
        (fun o G3 G2 G5 => D o G3 G2 G5 (patchT PE WE E))
        (@hyb3 (icPrg (patchT PE WE E)) (recB Hb st w c.2.1 (patchT P5 W5 c.2.2)) CrtGen.tables st w
          (c.1.1.2, c.1.2.2)
          (@hiddenOut (icPrg (patchT PE WE E)) st.params (ivOfPre Hb st c.1.1.2)
            (ba (deltaOf c.1.2.2)) c.1.1.1))
        c.1.2.2 (c.2.1, c.1.2.1, patchT P5 W5 c.2.2))
    (fun E => @zk_pre_h4Φ (icPrg (patchT PE WE E)) Hb st w (patchT P5 W5) cs hlr hzk hHb
      (fun o G3 G2 G5 => D o G3 G2 G5 (patchT PE WE E))
      (fun o G3 G2 G5 => Q3 o G3 G2 G5 (patchT PE WE E))
      (fun o G3 G3' G2 G5 => hQ3 o G3 G3' G2 G5 (patchT PE WE E)) q3
      (fun o G3 G2 G5 => hq3 o G3 G2 G5 (patchT PE WE E)))
  have hB := joint3_h4P Hb CrtGen.tables st w hp hzk D QE hQE hqE (patchT P5 W5) PE WE
  have hC := abs_pr_avgE
    (fun (c : (Hidden st.params × (Bytes 16 × Grind)) × Vis2 st.params) (E : Cipher) =>
      @Dp (icPrg (patchT PE WE E)) Hb CrtGen.tables st
        (fun o G3 G2 G5 => D o G3 G2 G5 (patchT PE WE E))
        (@hyb3 (icPrg (patchT PE WE E)) (recB Hb st w c.2.1 (patchT P5 W5 c.2.2.2)) CrtGen.tables st
          w c.1.2 (hiddenIdeal (ba (deltaOf c.1.2.2)) c.1.1)) c.1.2.2 (vφ (patchT P5 W5) c.2))
    (fun (c : SimCoins st.params × Vis2 st.params) (E : Cipher) =>
      D (simulate st.params c.1) c.2.1
        (@simTab (icPrg (patchT PE WE E)) Hb CrtGen.tables st (patchT P5 W5 c.2.2.2)
          (simulate st.params c.1) c.1.1.2.1 c.2.2.1) (patchT P5 W5 c.2.2.2) (patchT PE WE E))
    (fun E => @zk_post_h4P (icPrg (patchT PE WE E)) Hb st w cs hlr hzk hHb
      (fun o G3 G2 G5 => D o G3 G2 G5 (patchT PE WE E))
      (fun o G3 G2 G5 => Q5 o G3 G2 G5 (patchT PE WE E))
      (fun o G3 G2 G5 G5' => hQ5 o G3 G2 G5 G5' (patchT PE WE E)) q5
      (fun o G3 G2 G5 => hq5 o G3 G2 G5 (patchT PE WE E)) P5 W5)
  refine (abs_sub_le _ _ _).trans ((add_le_add hA ((abs_sub_le _ _ _).trans
    (add_le_add hB hC))).trans (le_of_eq (by ring)))

/-- **`zk_rom_ic_h23P` with the grinding term numeric** (`grindBad_le_110`). -/
theorem zk_rom_ic_h23P_num {cs : ByteArray → ByteArray → System GF128}
    (hlr : st.params.labelRows = true)
    (hzk : ZKHyp CrtGen.tables st w cs) (hHb : HashesWF Hb) (hp : SmallParams st.params)
    (D : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Prop)
    (Q3 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G2 G5 E, (∀ k ∈ Q3 o G3 G2 G5 E, G3 k = G3' k) →
      (D o G3 G2 G5 E ↔ D o G3' G2 G5 E))
    {q3 : ℕ} (hq3 : ∀ o G3 G2 G5 E, (Q3 o G3 G2 G5 E).card ≤ q3)
    (Q5 : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset (Bytes 37))
    (hQ5 : ∀ o G3 G2 G5 G5' E, (∀ k ∈ Q5 o G3 G2 G5 E, G5 k = G5' k) →
      (D o G3 G2 G5 E ↔ D o G3 G2 G5' E))
    {q5 : ℕ} (hq5 : ∀ o G3 G2 G5 E, (Q5 o G3 G2 G5 E).card ≤ q5)
    (QE : Except String ByteArray → Tab3 → Tab2G st.params → Tab5F → Cipher → Finset Blk)
    (hQE : ∀ o G3 G2 G5 E E', (∀ k ∈ QE o G3 G2 G5 E, E k = E' k) →
      (D o G3 G2 G5 E ↔ D o G3 G2 G5 E'))
    {qE : ℕ} (hqE : ∀ o G3 G2 G5 E, (QE o G3 G2 G5 E).card ≤ qE)
    (P5 : Finset (Bytes 37)) (W5 : Tab5F) (PE : Finset Blk) (WE : Cipher) :
    |pr (((Bytes 16 × Tab2G st.params) × (Tab3 × Tab5F)) × Cipher) (fun c =>
        D (@Prover.prove (icPrg (patchT PE WE c.2))
          (recH Hb st w c.1.2.1 c.1.1.2 (patchT P5 W5 c.1.2.2)) CrtGen.tables st w
          (ba c.1.1.1) st.params.witnessBytes) c.1.2.1 c.1.1.2 (patchT P5 W5 c.1.2.2)
          (patchT PE WE c.2)) -
      pr ((SimCoins st.params × Vis2 st.params) × Cipher) (fun c =>
        D (simulate st.params c.1.1) c.1.2.1
          (@simTab (icPrg (patchT PE WE c.2)) Hb CrtGen.tables st (patchT P5 W5 c.1.2.2.2)
            (simulate st.params c.1.1) c.1.1.1.2.1 c.1.2.2.1) (patchT P5 W5 c.1.2.2.2)
          (patchT PE WE c.2))| ≤
      q3 / 2 ^ 128 + 1 / 2 ^ 110 + 221 * (4607 + (qE + 4607) + PE.card) / 2 ^ 128 +
        ((q5 + 1) / 2 ^ 128 + (P5.card + 1) / 2 ^ 128) :=
  (zk_rom_ic_h23P Hb st w hlr hzk hHb hp D Q3 hQ3 hq3 Q5 hQ5 hq5 QE hQE hqE P5 W5 PE WE).trans
    (add_le_add (add_le_add (add_le_add le_rfl grindBad_le_110) le_rfl) le_rfl)

end ICP

end VoleMole.ZK.Sim
