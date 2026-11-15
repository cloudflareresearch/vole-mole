import VoleMole.ZK.HopsH4Pt
import VoleMole.ZK.IvOverlap
import VoleMole.ZK.HopsROMExp

/-!
# Audit of the point-level, expected-charge zero-knowledge hops

* `hide_rom_query_pt` (H4 at points) with the reader that reads nothing (`Q = ∅`, `qm = 0`) gives
  `221·4607·2⁻¹²⁸`, `hideHypIC_holds`'s bound; with a reader of one fixed point at a CTR block of
  the proof's `iv` (a consistent reader, `qm = 1`) it gives `221·4608/(2¹²⁸ − 221)`.
* `exP_sum_inY_le` at `N ≤ 2³¹` proofs: the reads charged to all proofs at once are at most
  `5/4` times the read budget.
* `h3_rom_query_real` (H1 with an expected charge) with the reader that reads nothing gives `0`.

No `sorry`, no `axiom`.
-/

set_option synthInstance.maxSize 1024

namespace VoleMole.Audit.ZKPoint

open VoleMole.Privacy VoleMole.ZK VoleMole.ZK.Sim VoleMole.ZK.IC VoleMole.Verifier

variable [VoleMole.Verifier.HasPrg]

/-- H4 at points against a distinguisher that reads no table: the ideal-cipher H4 bound. -/
example (p : Params) (iv delta : ByteArray) (hp : SmallParams p) (A : Hidden p → Prop) :
    |realPr (fun seed E => hiddenOutE E p iv delta seed) (fun o (_ : Cipher) => A o) -
        idealPr (hiddenIdeal (p := p) delta) (fun o (_ : Cipher) => A o)| ≤ 221 * 4607 / 2 ^ 128 := by
  have h := hide_rom_query_pt p iv delta hp (fun o (_ : Cipher) => A o) (fun _ _ => (∅ : Finset (Blk × Blk)))
    (fun _ _ _ _ => Iff.rfl) (fun _ _ _ _ => rfl) (qm := 0)
    (fun _ _ => by simp only [qkeys, Finset.filter_empty, Finset.image_empty, Finset.card_empty,
      le_refl]) (by norm_num)
  have e : expKeysY p iv delta (fun _ _ => (∅ : Finset (Blk × Blk))) = 0 := by
    unfold expKeysY
    simp only [qkeys, Finset.filter_empty, Finset.image_empty, Finset.card_empty, Nat.cast_zero]
    exact exP_const 0
  rw [e] at h
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

/-- H4 at points against a distinguisher that reads one fixed point, a CTR block of `iv`. -/
example (p : Params) (iv delta : ByteArray) (hp : SmallParams p) (k0 : Blk) :
    |realPr (fun seed E => hiddenOutE E p iv delta seed) (fun _ G => G k0 (xIn iv 1) = 0) -
        idealPr (hiddenIdeal (p := p) delta) (fun _ G => G k0 (xIn iv 1) = 0)| ≤
      221 * (4607 + 1) / (2 ^ 128 - 221) := by
  let Q : Hidden p → Cipher → Finset (Blk × Blk) := fun _ _ => {(k0, xIn iv 1)}
  have hq1 : ∀ o G, (qkeys (InY iv) (Q o G)).card ≤ 1 := fun o G =>
    (qkeys_card_le _).trans ((Finset.card_filter_le _ _).trans (by simp [Q]))
  have h := hide_rom_query_pt p iv delta hp (fun _ G => G k0 (xIn iv 1) = 0) Q
    (fun o G G' hG => by rw [hG (k0, xIn iv 1) (Finset.mem_singleton_self _)])
    (fun _ _ _ _ => rfl) hq1 (by norm_num)
  have hE : expKeysY p iv delta Q ≤ 1 := by
    unfold expKeysY
    exact (exP_mono (g := fun _ => (1 : ℝ)) fun s => by
      exact_mod_cast hq1 (hiddenOutE s.2 p iv delta s.1) s.2).trans (le_of_eq (exP_const 1))
  rw [Nat.cast_one, mul_one] at h
  refine h.trans (div_le_div_of_nonneg_right ?_ (by norm_num : (0 : ℝ) ≤ 2 ^ 128 - 221))
  linarith

/-- With `N ≤ 2³¹` independent uniform `iv`s, the reads charged to all proofs at once are at most
`5/4` times the read budget. -/
example {N : ℕ} (hN : N ≤ 2 ^ 31) (Z : (Fin N → Bytes 16) → Finset Blk) {q : ℕ}
    (hq : ∀ g, (Z g).card ≤ q) :
    exP (Fin N → Bytes 16) (fun g => ((∑ i, ((Z g).filter fun z => InY (ba (g i)) z).card : ℕ) : ℝ)) ≤
      q * (5 / 4) := by
  refine (exP_sum_inY_le Z hq).trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  have hN' : (N : ℝ) ≤ 2 ^ 31 := by exact_mod_cast hN
  have : (N : ℝ) ^ 2 ≤ (2 ^ 31) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hN' 2
  have h2 : (N : ℝ) ^ 2 / 2 ^ 64 ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]; norm_num at this ⊢; linarith
  linarith

/-- H1 with an expected charge against a distinguisher that reads no table: `0`. -/
example (Hs : Hashes) (mu1 wPrefix : ByteArray) (A : Bytes 16 × Bytes 16 → Prop) :
    |pr (Bytes 16 × (Bytes 16 → Bytes 32)) (fun p =>
        A (h3Seed (Hs.withTable .h3 (seedInput mu1 wPrefix) p.2) mu1 wPrefix (ba p.1))) -
      pr (Bytes 16 × ((Bytes 16 → Bytes 32) × Bytes 32)) (fun p => A (splitSeed p.2.2))| ≤ 0 := by
  have h := h3_rom_query_real (mu1 := mu1) (wPrefix := wPrefix) Hs (fun v _ => A v)
    (fun _ _ => ∅) (fun _ _ _ _ => Iff.rfl) (fun _ _ _ _ => rfl) (qm := 0) (fun _ _ => by simp)
    (by norm_num)
  simp only [Finset.card_empty, Nat.cast_zero, exP_const, zero_div] at h
  exact h

end VoleMole.Audit.ZKPoint
