import VoleMole.Arith.GFField
import VoleMole.Arith.Concrete

/-!
# The relations' soundness at the concrete GF(2¹²⁸)

The completeness and soundness theorems of `UOV.lean`, `PomFRIT.lean`, `Moussaka.lean` and
`Ratatouille.lean` are stated over an abstract field `F` of characteristic 2, with the GF(256)
embedding facts `IsEmbedding β toBits ofByte` and `β 0 = 1` as hypotheses; `Concrete.lean` fixes the
GF(256) side. `Arith/GFField.lean` makes the executable `GF128` a field (`instField`, keeping
`GF.lean`'s `0`, `1`, `+`, `*`) of characteristic 2 with `2¹²⁸` elements (`card_eq`), so here
everything is instantiated at `F := GF128`, `β := beta`, `K := GF256`: the hypotheses are discharged
by `isEmbedding` and `beta_zero` (both kernel-checked), `|F|` is `2¹²⁸`, and the GF(256) relations
are the byte equalities of `Concrete.lean`. These are the systems the executable verifier evaluates
(`Verifier/Relations.lean`, via `Verifier/Bridge/Relations.lean`).

## Main results

* `card_fun_gf128`: `|GF128^M| = (2¹²⁸)^M`.
* `UOV.uov_sound_gf128`, `UOV.uov_card_bad_gf128`: the UOV gadget, with `ι = iota`
  (`embed_toBits`) and the decoded bytes as witness bytes.
* `PomFRIT.pomfrit_complete_gf128`, `PomFRIT.pomfrit_sound_card_gf128`;
  `Moussaka.issue_sound_gf128`, `Moussaka.redeem_complete_gf128`,
  `Moussaka.redeem_sound_card_gf128`; `Ratatouille.issue_sound_gf128`,
  `Ratatouille.spend_complete_gf128`, `Ratatouille.spend_sound_card_gf128`: no hypotheses beyond
  the instance's (`|anchors| ≤ 64`, `d < 2⁶⁴`); the bad-`l` bound reads
  `#bad · 2¹²⁸ ≤ (2¹²⁸)^M`, i.e. probability `≤ 2⁻¹²⁸`.
-/

open Finset

namespace VoleMole.Arith

open UOV Keccak

theorem card_fun_gf128 (M : ℕ) : Fintype.card (Fin M → GF128) = (2 ^ 128) ^ M := by
  rw [Fintype.card_fun, Fintype.card_fin, GF128.card_eq]

/-! ## The UOV gadget -/

namespace UOV

/-- `uov_sound` at `GF128`: the bits of `s` are bits, and their bytes `σ` satisfy
`Σ_k l_k (ι(P(σ)_k) + ι(t_k)) = 0`. -/
theorem uov_sound_gf128 (N M : ℕ) (pk : ℕ → GF256) (l : Fin M → GF128) (o : ℕ)
    (t : Fin M → GF256) (w : ℕ → GF128) (h : (uovSystem beta GF256.toBits N M pk l o t).Holds w) :
    ∃ wb : ℕ → Bool, (∀ n < 8 * N, w (8 * o + n) = bitF (wb (8 * o + n))) ∧
      ∑ k, l k * (iota (publicMap N M pk (fun i => ⟨Keccak.witByte wb (o + i)⟩) k) +
        iota (t k)) = 0 := by
  obtain ⟨wb, hb, hs⟩ := uov_sound isEmbedding N M pk l o t w h
  refine ⟨wb, hb, ?_⟩
  have hd : decode GF256.ofBits wb o = fun i => ⟨Keccak.witByte wb (o + i)⟩ :=
    funext (decode_gf256 wb o)
  simpa only [embed_toBits, hd] using hs

/-- `uov_card_bad` at `GF128`: if `P(σ) ≠ t`, exactly a `2⁻¹²⁸` fraction of the `l` make the
combination vanish. -/
theorem uov_card_bad_gf128 {N M : ℕ} {pk : ℕ → GF256} {σ : ℕ → GF256} {t : Fin M → GF256}
    (h : publicMap N M pk σ ≠ t) :
    #{l : Fin M → GF128 | ∑ k, l k * (iota (publicMap N M pk σ k) + iota (t k)) = 0} * 2 ^ 128 =
      (2 ^ 128) ^ M := by
  have := uov_card_bad (F := GF128) isEmbedding h
  simp only [embed_toBits] at this
  rwa [GF128.card_eq, card_fun_gf128] at this

end UOV

/-! ## PomFRIT -/

namespace PomFRIT

/-- `pomfrit_complete` at `GF128`, from the byte relation `P(s)[k] = h[k] ⊕ r[k]`. -/
theorem pomfrit_complete_gf128 (N M : ℕ) (pk : ℕ → GF256) (h : Fin M → GF256)
    (l : Fin M → GF128) (wb : ℕ → Bool)
    (hrel : ∀ k : Fin M, (publicMap N M pk (fun i => ⟨Keccak.witByte wb (witOffS M + i)⟩) k).val =
      (h k).val ^^^ Keccak.witByte wb (witOffR + k)) :
    (pomfritRedeemSystem beta GF256.toBits N M pk h l).Holds (ofBits wb) :=
  pomfrit_complete isEmbedding N M pk h l wb ((pomfritRel_gf256_iff N M pk h wb).2 hrel)

open Classical in
/-- **PomFRIT redeem soundness at GF(2¹²⁸).** For committed values fixed before `l`: a bit vector
whose bytes satisfy `P(s) = h ⊕ r`, or at most a `2⁻¹²⁸` fraction of the `l` make the system
hold. -/
theorem pomfrit_sound_card_gf128 (N M : ℕ) (pk : ℕ → GF256) (h : Fin M → GF256) (w : ℕ → GF128) :
    (∃ wb : ℕ → Bool, (∀ i < witnessBits N M, w i = bitF (wb i)) ∧
        ∀ k : Fin M, (publicMap N M pk (fun i => ⟨Keccak.witByte wb (witOffS M + i)⟩) k).val =
          (h k).val ^^^ Keccak.witByte wb (witOffR + k)) ∨
      #{l : Fin M → GF128 | (pomfritRedeemSystem beta GF256.toBits N M pk h l).Holds w} * 2 ^ 128 ≤
        (2 ^ 128) ^ M := by
  have := pomfrit_sound_card_gf256 (F := GF128) isEmbedding N M pk h w
  rwa [GF128.card_eq, card_fun_gf128] at this

end PomFRIT

/-! ## Moussaka -/

namespace Moussaka

/-- `issue_sound` at `GF128` (no combination challenge, no hypotheses). -/
theorem issue_sound_gf128 (t : Fin M → UInt8) (ctxIss : ℕ → UInt8) (w : ℕ → GF128)
    (hw : (issueSystem t ctxIss).Holds w) :
    (∀ i < issueWitnessBits, w i = bitF (decide (w i = 1))) ∧
      issueRel t ctxIss (issueNf fun i => decide (w i = 1))
        (issueCtxRed fun i => decide (w i = 1)) (issueR fun i => decide (w i = 1)) :=
  issue_sound t ctxIss w hw

/-- `redeem_complete` at `GF128`, from the byte relation. -/
theorem redeem_complete_gf128 (anchors : List (ℕ → GF256)) (hn : anchors.length ≤ 64)
    (nf ctxIss ctxRed : ℕ → UInt8) (l : Fin M → GF128) (w : ℕ → Bool)
    (h5 : ∀ i < 800, w (8 * redeemOffStates + i) =
      stateBit (keccakP800Rounds 0 5 (encodeComState nf ctxIss ctxRed (redeemR w))) i)
    (h9 : ∀ i < 800, w (8 * (redeemOffStates + 100) + i) =
      stateBit (keccakP800Rounds 0 9 (encodeComState nf ctxIss ctxRed (redeemR w))) i)
    (u₀ : ℕ) (hsel : ∀ u < 64, w (selBit u) = decide (u = u₀)) (hu₀ : u₀ < anchors.length)
    (hrel : ∀ k : Fin M,
      (publicMap N M anchors[u₀] (fun i => ⟨Keccak.witByte w (redeemOffS + i)⟩) k).val =
        com nf ctxIss ctxRed (redeemR w) k) :
    (redeemSystem beta GF256.toBits anchors nf ctxIss ctxRed l).Holds (ofBits w) :=
  redeem_complete isEmbedding beta_zero anchors hn nf ctxIss ctxRed l w h5 h9 u₀ hsel
    ((redeemRel_gf256_iff anchors nf ctxIss ctxRed _ w u₀).2 ⟨hu₀, hrel⟩)

open Classical in
/-- **Moussaka redeem soundness at GF(2¹²⁸).** -/
theorem redeem_sound_card_gf128 (anchors : List (ℕ → GF256)) (hn : anchors.length ≤ 64)
    (nf ctxIss ctxRed : ℕ → UInt8) (w : ℕ → GF128) :
    (∃ wb : ℕ → Bool, (∀ i < redeemWitnessBits, w i = bitF (wb i)) ∧
        ∃ u₀, (∀ u < 64, wb (selBit u) = decide (u = u₀)) ∧ ∃ h : u₀ < anchors.length,
          ∀ k : Fin M,
            (publicMap N M anchors[u₀] (fun i => ⟨Keccak.witByte wb (redeemOffS + i)⟩) k).val =
              com nf ctxIss ctxRed (redeemR wb) k) ∨
      #{l : Fin M → GF128 | (redeemSystem beta GF256.toBits anchors nf ctxIss ctxRed l).Holds w} *
        2 ^ 128 ≤ (2 ^ 128) ^ M := by
  have := redeem_sound_card_gf256 (F := GF128) isEmbedding beta_zero anchors hn nf ctxIss ctxRed w
  rwa [GF128.card_eq, card_fun_gf128] at this

end Moussaka

/-! ## Ratatouille -/

namespace Ratatouille

/-- `issue_sound` at `GF128` (no combination challenge, no hypotheses). -/
theorem issue_sound_gf128 (c : ℕ → UInt8) (tInit : ℕ) (ctx : ℕ → UInt8) (w : ℕ → GF128)
    (h : (issueSystem c tInit ctx).Holds w) :
    (∀ i < 8 * issueWitnessBytes, w i = bitF (decide (w i = 1))) ∧
      IssueRel c tInit ctx (bytesAt (fun i => decide (w i = 1)) 16)
        (bytesAt (fun i => decide (w i = 1)) 0) :=
  issue_sound c tInit ctx w h

/-- `spend_complete` at `GF128`. -/
theorem spend_complete_gf128 (pk : ℕ → GF256) (nf : ℕ → UInt8) {d : ℕ} (hd : d < 2 ^ 64)
    (cNext ctx : ℕ → UInt8) (w : ℕ → Bool) (hrel : SpendRelOf GF256.ofBits pk nf d cNext ctx w)
    (hcom : ∀ k < 32, bytesAt w 32 k = commit nf ctx (creditAt w 16) (bytesAt w 0) k)
    (hc : SpendCarries d w) (hs : SpendStates nf ctx w) (l : Fin uovM → GF128) :
    (spendSystem beta GF256.toBits pk nf d cNext ctx l).Holds (ofBits w) :=
  spend_complete isEmbedding beta_zero pk nf hd cNext ctx w hrel hcom hc hs l

open Classical in
/-- **Ratatouille spend soundness at GF(2¹²⁸).** -/
theorem spend_sound_card_gf128 (pk : ℕ → GF256) (nf : ℕ → UInt8) {d : ℕ} (hd : d < 2 ^ 64)
    (cNext ctx : ℕ → UInt8) (w : ℕ → GF128) :
    (∃ wb : ℕ → Bool, (∀ i < 8 * spendWitnessBytes, w i = bitF (wb i)) ∧
        (∀ k : Fin uovM,
          (publicMap uovN uovM pk (fun i => ⟨Keccak.witByte wb (112 + i)⟩) k).val =
            stateByte (keccakP800 (tagState (commit nf ctx (creditAt wb 16) (bytesAt wb 0))
              (creditAt wb 24))) k.1) ∧
        (∀ k < 32, cNext k = commit (bytesAt wb 64) ctx (creditAt wb 88) (bytesAt wb 96) k) ∧
        creditAt wb 16 + creditAt wb 24 = creditAt wb 88 + d ∧ creditAt wb 16 < 2 ^ 64 ∧
        creditAt wb 24 < 2 ^ 64 ∧ creditAt wb 88 < 2 ^ 64 ∧ d < 2 ^ 64) ∨
      #{l : Fin uovM → GF128 | (spendSystem beta GF256.toBits pk nf d cNext ctx l).Holds w} *
          2 ^ 128 ≤ (2 ^ 128) ^ uovM := by
  have := spend_sound_card_gf256 (F := GF128) isEmbedding beta_zero pk nf hd cNext ctx w
  rwa [GF128.card_eq, card_fun_gf128] at this

end Ratatouille

end VoleMole.Arith
