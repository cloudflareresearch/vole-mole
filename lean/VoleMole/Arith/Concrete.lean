import VoleMole.Arith.GFEmbedding
import VoleMole.Arith.PomFRIT
import VoleMole.Arith.Moussaka
import VoleMole.Arith.Ratatouille

/-!
# The relations on the concrete GF(256): plain byte equalities

The relations of `PomFRIT.lean`, `Moussaka.lean` and `Ratatouille.lean` are stated over an abstract
GF(256) model `K` with a decoder `ofByte`. Here they are instantiated with pqov's GF(256)
(`K := GF256`, `ofByte := GF256.ofBits`, `Arith/GF.lean`), where a decoded byte is the byte itself
(`GF256.ofBits_getLsbD`, `decode_gf256`). The UOV equations then read as equalities of bytes, i.e.
as the C++ checks: `PublicKey::eval(s) == h ⊕ r` (PomFRIT), `anchors[u₀].eval(s) == Com(…)`
(Moussaka), `pk.eval(s) == Tag(Com(…), x)` (Ratatouille), with `P(s)` computed by
`UOV.publicMap` (= pqov's `ov_publicmap`, `Pqov.ovPublicmap_eq_publicMap`).

## Concrete soundness

The soundness theorems need `[Field F] [CharP F 2]`, which `GF128` deliberately lacks, so they
cannot be instantiated at `F := GF128`. The corollaries below fix the K side (`K := GF256`,
`toBits := GF256.toBits`, `ofByte := GF256.ofBits`) and state the conclusion in byte form; the
remaining hypotheses are `IsEmbedding β GF256.toBits GF256.ofBits` and `β 0 = 1` on the abstract
`F`. For the concrete `β := beta` both are proved (`isEmbedding`, `beta_zero`); only the `Field`
instance on `GF128` is missing to close the instantiation.

## Main results

* `GF256.ofBits_getLsbD`, `decode_gf256`, `beta_zero`.
* `PomFRIT.pomfritRel_gf256_iff`, `Moussaka.toK_gf256`, `Moussaka.redeemRel_gf256_iff`,
  `Ratatouille.ofUInt8_gf256`, `Ratatouille.spendRelOf_gf256_iff`: the relations as byte equalities.
* `PomFRIT.pomfrit_sound_card_gf256`, `Moussaka.redeem_sound_card_gf256`,
  `Ratatouille.spend_sound_card_gf256`: the end-to-end soundness theorems with the byte relations.
-/

open Finset

namespace VoleMole.Arith

open UOV Keccak

theorem GF256.ofBits_getLsbD_all : ∀ n : Fin 256,
    GF256.ofBits (fun j => (n.val.toUInt8).toBitVec.getLsbD j.val) = ⟨n.val.toUInt8⟩ := by
  decide +kernel

/-- Decoding the bits of a byte gives the byte. -/
theorem GF256.ofBits_getLsbD (b : UInt8) : GF256.ofBits (fun j => b.toBitVec.getLsbD j.val) = ⟨b⟩ := by
  have := GF256.ofBits_getLsbD_all ⟨b.toNat, b.toNat_lt⟩
  simpa only [UInt8.ofNat_toNat] using this

/-- A decoded witness byte is the witness byte `witByte`. -/
theorem decode_gf256 (w : ℕ → Bool) (o i : ℕ) :
    decode GF256.ofBits w o i = ⟨Keccak.witByte w (o + i)⟩ := by
  rw [← GF256.ofBits_getLsbD]
  unfold decode
  congr 1
  funext j
  rw [Ratatouille.witByte_bit w _ j j.isLt]

/-- `β 0 = 1` for the concrete constants. -/
theorem beta_zero : beta 0 = 1 := rfl

theorem GF256.mk_inj {a b : UInt8} : (⟨a⟩ : GF256) = ⟨b⟩ ↔ a = b := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; rfl

theorem GF256.funext_iff {M : ℕ} {f g : Fin M → GF256} : f = g ↔ ∀ k, (f k).val = (g k).val :=
  ⟨fun h k => by rw [h], fun h => funext fun k => GF256.ext' (h k)⟩

/-! ## PomFRIT -/

namespace PomFRIT

/-- **PomFRIT on bytes.** `P(σ) = h + ρ` with `σ`, `ρ` the witness bytes is the byte check
`P(s)[k] = h[k] ⊕ r[k]` (`pomfrit.cpp:174-175`). -/
theorem pomfritRel_gf256_iff (N M : ℕ) (pk : ℕ → GF256) (h : Fin M → GF256) (wb : ℕ → Bool) :
    pomfritRel N M pk h (decodeR GF256.ofBits wb M) (decodeS GF256.ofBits wb M) ↔
      ∀ k : Fin M, (publicMap N M pk (fun i => ⟨Keccak.witByte wb (witOffS M + i)⟩) k).val =
        (h k).val ^^^ Keccak.witByte wb (witOffR + k) := by
  have hs : decode GF256.ofBits wb (witOffS M) = fun i => ⟨Keccak.witByte wb (witOffS M + i)⟩ :=
    funext (decode_gf256 wb (witOffS M))
  simp only [pomfritRel, decodeR, decodeS, hs, decode_gf256, GF256.funext_iff, GF256.add_val]

variable {F : Type*} [Field F] [CharP F 2] {β : Fin 8 → F}

open Classical in
/-- `pomfrit_sound_card` on the concrete GF(256), with the byte relation. -/
theorem pomfrit_sound_card_gf256 [Fintype F] [DecidableEq F]
    (hι : IsEmbedding β GF256.toBits GF256.ofBits) (N M : ℕ) (pk : ℕ → GF256) (h : Fin M → GF256)
    (w : ℕ → F) :
    (∃ wb : ℕ → Bool, (∀ i < witnessBits N M, w i = bitF (wb i)) ∧
        ∀ k : Fin M, (publicMap N M pk (fun i => ⟨Keccak.witByte wb (witOffS M + i)⟩) k).val =
          (h k).val ^^^ Keccak.witByte wb (witOffR + k)) ∨
      #{l : Fin M → F | (pomfritRedeemSystem β GF256.toBits N M pk h l).Holds w} *
          Fintype.card F ≤ Fintype.card (Fin M → F) := by
  rcases pomfrit_sound_card hι N M pk h w with ⟨wb, hb, hr⟩ | h
  · exact Or.inl ⟨wb, hb, (pomfritRel_gf256_iff N M pk h wb).1 hr⟩
  · exact Or.inr h

end PomFRIT

/-! ## Moussaka -/

namespace Moussaka

theorem toK_gf256 (x : UInt8) : toK GF256.ofBits x = ⟨x⟩ := GF256.ofBits_getLsbD x

/-- **Moussaka redeem on bytes.** The selected Anchor's public map at the witness bytes `s` equals
the commitment bytes: `anchors[u₀].eval(s) == Com(nf, ctx_iss, ctx_red, r)`. -/
theorem redeemRel_gf256_iff (anchors : List (ℕ → GF256)) (nf ctxIss ctxRed r : ℕ → UInt8)
    (wb : ℕ → Bool) (u₀ : ℕ) :
    redeemRel GF256.ofBits anchors nf ctxIss ctxRed r (redeemS GF256.ofBits wb) u₀ ↔
      ∃ h : u₀ < anchors.length, ∀ k : Fin M,
        (publicMap N M anchors[u₀] (fun i => ⟨Keccak.witByte wb (redeemOffS + i)⟩) k).val =
          com nf ctxIss ctxRed r k := by
  have hs : redeemS GF256.ofBits wb = fun i => ⟨Keccak.witByte wb (redeemOffS + i)⟩ :=
    funext (decode_gf256 wb redeemOffS)
  simp only [redeemRel, hs, redeemTarget, toK_gf256, GF256.funext_iff]

variable {F : Type*} [Field F] [CharP F 2] {β : Fin 8 → F}

open Classical in
/-- `redeem_sound_card` on the concrete GF(256), with the byte relation. -/
theorem redeem_sound_card_gf256 [Fintype F] [DecidableEq F]
    (hι : IsEmbedding β GF256.toBits GF256.ofBits) (hβ : β 0 = 1) (anchors : List (ℕ → GF256))
    (hn : anchors.length ≤ 64) (nf ctxIss ctxRed : ℕ → UInt8) (w : ℕ → F) :
    (∃ wb : ℕ → Bool, (∀ i < redeemWitnessBits, w i = bitF (wb i)) ∧
        ∃ u₀, (∀ u < 64, wb (selBit u) = decide (u = u₀)) ∧ ∃ h : u₀ < anchors.length,
          ∀ k : Fin M,
            (publicMap N M anchors[u₀] (fun i => ⟨Keccak.witByte wb (redeemOffS + i)⟩) k).val =
              com nf ctxIss ctxRed (redeemR wb) k) ∨
      #{l : Fin M → F | (redeemSystem β GF256.toBits anchors nf ctxIss ctxRed l).Holds w} *
        Fintype.card F ≤ Fintype.card (Fin M → F) := by
  rcases redeem_sound_card hι hβ anchors hn nf ctxIss ctxRed w with ⟨wb, hb, u₀, hs, hr⟩ | h
  · exact Or.inl ⟨wb, hb, u₀, hs, (redeemRel_gf256_iff anchors nf ctxIss ctxRed _ wb u₀).1 hr⟩
  · exact Or.inr h

end Moussaka

/-! ## Ratatouille -/

namespace Ratatouille

theorem ofUInt8_gf256 (b : UInt8) : ofUInt8 GF256.ofBits b = ⟨b⟩ := GF256.ofBits_getLsbD b

/-- **Ratatouille spend on bytes.** V1 reads `pk.eval(s) == Tag(Com(nf, ctx, t, r), x)` as bytes;
V2–V4 are unchanged (they never mention `K`). -/
theorem spendRelOf_gf256_iff (pk : ℕ → GF256) (nf : ℕ → UInt8) (d : ℕ) (cNext ctx : ℕ → UInt8)
    (w : ℕ → Bool) :
    SpendRelOf GF256.ofBits pk nf d cNext ctx w ↔
      (∀ k : Fin uovM, (publicMap uovN uovM pk (fun i => ⟨Keccak.witByte w (112 + i)⟩) k).val =
          stateByte (keccakP800 (tagState (commit nf ctx (creditAt w 16) (bytesAt w 0))
            (creditAt w 24))) k.1) ∧
        (∀ k < 32, cNext k = commit (bytesAt w 64) ctx (creditAt w 88) (bytesAt w 96) k) ∧
        creditAt w 16 + creditAt w 24 = creditAt w 88 + d ∧ creditAt w 16 < 2 ^ 64 ∧
        creditAt w 24 < 2 ^ 64 ∧ creditAt w 88 < 2 ^ 64 ∧ d < 2 ^ 64 := by
  have hs : decode GF256.ofBits w 112 = fun i => ⟨Keccak.witByte w (112 + i)⟩ :=
    funext (decode_gf256 w 112)
  simp only [SpendRelOf, SpendRel, hs, tagTarget, ofUInt8_gf256, GF256.funext_iff]

variable {F : Type*} [Field F] [CharP F 2] {β : Fin 8 → F}

open Classical in
/-- `spend_sound_card` on the concrete GF(256), with the byte relation. -/
theorem spend_sound_card_gf256 [Fintype F] [DecidableEq F]
    (hι : IsEmbedding β GF256.toBits GF256.ofBits) (hβ : β 0 = 1) (pk : ℕ → GF256)
    (nf : ℕ → UInt8) {d : ℕ} (hd : d < 2 ^ 64) (cNext ctx : ℕ → UInt8) (w : ℕ → F) :
    (∃ wb : ℕ → Bool, (∀ i < 8 * spendWitnessBytes, w i = bitF (wb i)) ∧
        (∀ k : Fin uovM,
          (publicMap uovN uovM pk (fun i => ⟨Keccak.witByte wb (112 + i)⟩) k).val =
            stateByte (keccakP800 (tagState (commit nf ctx (creditAt wb 16) (bytesAt wb 0))
              (creditAt wb 24))) k.1) ∧
        (∀ k < 32, cNext k = commit (bytesAt wb 64) ctx (creditAt wb 88) (bytesAt wb 96) k) ∧
        creditAt wb 16 + creditAt wb 24 = creditAt wb 88 + d ∧ creditAt wb 16 < 2 ^ 64 ∧
        creditAt wb 24 < 2 ^ 64 ∧ creditAt wb 88 < 2 ^ 64 ∧ d < 2 ^ 64) ∨
      #{l : Fin uovM → F | (spendSystem β GF256.toBits pk nf d cNext ctx l).Holds w} *
          Fintype.card F ≤ Fintype.card (Fin uovM → F) := by
  rcases spend_sound_card hι hβ pk nf hd cNext ctx w with ⟨wb, hb, hr⟩ | h
  · exact Or.inl ⟨wb, hb, (spendRelOf_gf256_iff pk nf d cNext ctx wb).1 hr⟩
  · exact Or.inr h

end Ratatouille

end VoleMole.Arith
