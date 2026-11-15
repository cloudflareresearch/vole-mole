import VoleMole.ZK.HopsH4Ideal
import VoleMole.ZK.IdealCipherPt
import VoleMole.ZK.ReadsPoint

/-!
# Hop H4 at points: the cipher charged only at the CTR blocks of the proof's `iv`

`hide_rom_query` (`ZK/HopsH4Ideal.lean`) bounds H4 in the ideal-cipher model by
`221·(4607 + q)/2¹²⁸` for a distinguisher that reads the table at `q` keys (whole rows), `q` a
worst-case budget. A read at a hidden node's key costs the same whatever its input.

The commitment reads every row only at the CTR blocks of its `iv` (`InY iv`: `prgR` and the GGM
inputs `xIn`, `hidOfRows_congrPt`). So the hidden rows need only be replaced at those blocks
(`IC.puncturePt`), and a hop is charged only for the distinguisher's reads `(k, z)` with `z` a
CTR block of `iv`. With the charge moved to the real experiment (`IC.puncturePt_real`):

    hide_rom_query_pt:
      |Pr_real[A] − Pr_ideal[A]| ≤ 221·(4607 + E_real[#keys A reads at CTR blocks of iv])
                                     / (2¹²⁸ − 221·qm),

for a consistent reader (`hQc`) that reads at most `qm` such keys (`hqm`, `221·qm < 2¹²⁸`). The
expectation is over the root seed and the table in the real experiment. A read at an input that is
not a CTR block of `iv` (for instance a CTR block of another proof's `iv`, `lane1_of_ctrBlock_eq`)
costs nothing; the worst case `qm` enters only through the denominator, a factor
`1 + O(221·qm·2⁻¹²⁸)`.

Function rows only (the PRF view of the ideal cipher), as `hide_rom_query`.
-/

open Finset

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.ZK.Sim

variable [VoleMole.Verifier.HasPrg]

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.Privacy VoleMole.ZK.IC

/-- Membership in the CTR blocks of an `iv`, decided classically (for `IC.qkeys`). -/
noncomputable instance inY_decPred (iv : ByteArray) : DecidablePred (InY iv) := Classical.decPred _

/-- Every GGM input is a CTR block of the `iv`. -/
lemma xIn_inY (iv : ByteArray) (c : ℕ) : InY iv (xIn iv c) := ⟨_, _, rfl⟩

/-- `prgR` reads its row only at CTR blocks of its `iv`. -/
lemma prgR_congrY {r r' : Blk → Blk} {iv : ByteArray} (h : ∀ z, InY iv z → r z = r' z)
    (t c : UInt32) (n : ℕ) : prgR r iv t c n = prgR r' iv t c n :=
  prgR_congr fun _ _ => h _ ⟨_, _, rfl⟩

/-- **The hidden part reads the rows only at the CTR blocks of the `iv`.** -/
theorem hidOfRows_congrPt (p : Params) (iv delta : ByteArray) (ρ ρ' : ℕ → Blk → Blk)
    (h : ∀ m < nN, ∀ z, InY iv z → ρ m z = ρ' m z) :
    hidOfRows p iv delta ρ = hidOfRows p iv delta ρ' := by
  have h3 : usR p iv ρ = usR p iv ρ' := by
    unfold usR
    refine Array.map_congr_left fun i hi => ?_
    have hi := Array.mem_range.1 hi
    refine congrArg bytesOfWords ?_
    unfold smallR
    refine List.foldl_ext _ _ _ fun acc j hj => ?_
    rw [prgR_congrY (h _ (treePos_lt hi (List.mem_range.1 hj)))]
  unfold hidOfRows
  rw [h3, prgR_congrY (h 0 (by decide))]
  refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun k => ?_) rfl)
  · simp only [prgR_congrY (h _ (hLeaf_lt delta i.isLt))]
  · simp only
    split_ifs with hk
    · rw [h _ (by have := oNode_lt delta hk; omega) _ (xIn_inY iv _)]
    · rfl

variable (p : Params) (iv delta : ByteArray)

/-- **The expected number of keys read at the CTR blocks of `iv`**, in the real experiment (a
uniform root seed and a uniform table). -/
noncomputable def expKeysY (Q : Hidden p → Cipher → Finset (Blk × Blk)) : ℝ :=
  exP (Blk × Cipher) (fun s => ((qkeys (InY iv) (Q (hiddenOutE s.2 p iv delta s.1) s.2)).card : ℝ))

/-- **H4 at points in the ideal-cipher model**: for a consistent reader `Q` of the table (`hQ`,
`hQc`) that reads at most `qm` keys at CTR blocks of `iv`, with `221·qm < 2¹²⁸`, the advantage
between the hidden part of a commitment from a uniform root seed and the ideal hidden part is at
most

    221·(4607 + E_real[#keys read at CTR blocks of iv]) / (2¹²⁸ − 221·qm),

the expectation over the real experiment (`expKeysY`). -/
theorem hide_rom_query_pt (hp : SmallParams p) (A : Hidden p → Cipher → Prop)
    (Q : Hidden p → Cipher → Finset (Blk × Blk))
    (hQ : ∀ o G G', (∀ kz ∈ Q o G, G kz.1 kz.2 = G' kz.1 kz.2) → (A o G ↔ A o G'))
    (hQc : ∀ o G G', (∀ kz ∈ Q o G, G kz.1 kz.2 = G' kz.1 kz.2) → Q o G = Q o G')
    {qm : ℕ} (hqm : ∀ o G, (qkeys (InY iv) (Q o G)).card ≤ qm)
    (hsmall : 221 * (qm : ℝ) < 2 ^ 128) :
    |realPr (fun seed E => hiddenOutE E p iv delta seed) A - idealPr (hiddenIdeal (p := p) delta) A| ≤
      221 * (4607 + expKeysY p iv delta Q) / (2 ^ 128 - 221 * qm) := by
  have hc : ((hidSet delta).card : ℝ) ≤ 221 := by exact_mod_cast hidSet_card delta
  have hs : ((hidSet delta).card : ℝ) * qm < Fintype.card Blk := by
    rw [card_blk]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)) (by exact_mod_cast hsmall)
  have h := puncturePt_real (x := xIn iv) (N := nN) (P := InY iv) (fun n => hid delta n = true)
    (fun n hn hs h0 => hid_parent delta (by omega) hn hs)
    (fun n _ _ h0 m hm hmn hp => xIn_sib iv hm h0 hmn hp) (xIn_inY iv) (hidOfRows p iv delta)
    (fun n hn hs h0 ρ y => hidOfRows_point p iv delta hn h0 hs ρ y)
    (fun ρ ρ' hsec hns => hidOfRows_congrPt p iv delta ρ ρ' fun m hm z hz => by
      by_cases hm' : hid delta m = true
      · exact hsec m hm hm' z hz
      · rw [hns m hm hm'])
    A Q hQ hQc hqm hs
  have e : ((range nN).filter fun n => hid delta n = true) = hidSet delta := rfl
  have hN : nN = 4607 := rfl
  have hcK : (Fintype.card Blk : ℝ) = 2 ^ 128 := by exact_mod_cast card_blk
  rw [e, exper_empty, exper_final p iv delta hp A, exP_empty (x := xIn iv) (N := nN)
    (hidOfRows p iv delta) (fun o G => ((qkeys (InY iv) (Q o G)).card : ℝ)), hcK] at h
  refine h.trans ?_
  have hE : 0 ≤ expKeysY p iv delta Q := exP_nonneg fun _ => Nat.cast_nonneg _
  have hden : (0 : ℝ) < 2 ^ 128 - 221 * qm := by linarith
  have hnum : ((hidSet delta).card : ℝ) * ((nN : ℕ) + expKeysY p iv delta Q) ≤
      221 * (4607 + expKeysY p iv delta Q) := by
    rw [hN]; push_cast
    exact mul_le_mul_of_nonneg_right hc (by linarith)
  refine div_le_div₀ (by linarith) hnum hden ?_
  nlinarith [Nat.cast_nonneg (α := ℝ) qm]

/-- The expected number of keys read at CTR blocks of `iv` is at most the expected number of
read points at CTR blocks of `iv`. -/
lemma expKeysY_le (Q : Hidden p → Cipher → Finset (Blk × Blk)) :
    expKeysY p iv delta Q ≤ exP (Blk × Cipher) (fun s =>
      (((Q (hiddenOutE s.2 p iv delta s.1) s.2).filter fun kz => InY iv kz.2).card : ℝ)) :=
  exP_mono fun _ => by exact_mod_cast qkeys_card_le _

end VoleMole.ZK.Sim
