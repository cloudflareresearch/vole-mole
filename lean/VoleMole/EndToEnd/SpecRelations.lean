import VoleMole.Privacy.RatatouilleLean

/-!
# From the arithmetized relations back to the spec relations

The soundness theorems of the random-oracle layer (`ROM/CipherFull.lean`, `ROM/PermFull.lean`,
`ROM/AdaptFull.lean`, `ROM/AdaptComb.lean`, `ROM/AdaptPomfrit.lean`, `ROM/PermAdapt.lean`) bound
the probability that the verifier accepts and no known tree's candidate `w : ℕ → GF128` satisfies
the *arithmetized* relation (`EndToEnd/Relations.lean`: `moussakaIssueWit`, `moussakaRedeemWit`,
`ratatouilleIssueWit`, `ratatouilleSpendWit`, `pomfritWit`). Those are stated on byte functions
(`fnOf b : ℕ → UInt8`, zero beyond the end), and `Privacy/MoussakaLean.lean`,
`Privacy/RatatouilleLean.lean`, `Privacy/PomFRITLean.lean` prove spec → arithmetized (the spec
witness encodings satisfy the systems). This file proves the converse: **an arithmetized witness
decodes to a witness of the spec relation**, for well-formed instances, so the bounds hold for the
spec relations too (`ROM/SpecSound.lean`).

## The decoded witness

The extracted candidate `w` is decoded bitwise (`bitsOf w i = (w i = 1)`; on the witness rows
the arithmetized relation makes `w` a bit vector, `bitsOf_eq`), and the spec witness is built from
the decoded fields at the witness layout of `Arith/*` (= `encode_*_witness` of the C++):

| relation | spec relation | decoded witness | well-formedness |
| --- | --- | --- | --- |
| Moussaka issue | `Privacy.Moussaka.IssueRelW` (`Spec.Moussaka.IssueRel` + 16-byte `ctx_iss`) | `issueWitOf`: `r`, `ctx_red`, `nf` at bytes 0, 16, 32, re-encoded by `encodeIssueWitness` | `|t| = 45`, `|ctx_iss| = 16` |
| Moussaka redeem | `Privacy.Moussaka.RedeemRelW` | `redeemWitOf`: `r`, `s` at 0, 16, the selected index (first set selector bit), re-encoded by `encodeRedeemWitness` | `|anchors| ≤ 64`, `|nf| = 24`, contexts 16 |
| Ratatouille issue | `Spec.Ratatouille.IssueRel` | `issueWitOfR`: `nf` at 16, `r` at 0 | spec-typed instance (`bOf`), or byte arrays read as vectors (`issueInstOf`) with `t_init < 2⁶⁴` |
| Ratatouille spend | `Spec.Ratatouille.SpendRel` | `spendWitOf`: `r`, `t`, `x`, `nf'`, `t'`, `r'`, `s` at 0, 16, 24, 64, 88, 96, 112 | spec-typed with `pk.map = x.pk`, or `spendInstOf` with `d < 2⁶⁴` |
| PomFRIT redeem | `PomRel` (`Spec.PomFRIT.Correct.complete`'s `P(s) = h ⊕ r`) | `r`, `s` at 0, 45 | none (`|h| = 45` holds) |

For the three relations with Keccak states in the witness (Moussaka issue and redeem, Ratatouille
spend's encoding) the spec witness is the *re-encoding* of the decoded fields: the committed states
are recomputed from the decoded opening (`encode_committed_states`), not read off the candidate.
(The arithmetized predicates record the decoded fields only; the systems also force the committed
states to be the honest ones, `Arith.Keccak.qsKeccak_holds_iff_bytes`, but the predicates the bounds
are stated for do not carry that.) The spec relation is `∃ fields, w = encode(fields) ∧ …`, so this
is exactly "the decoded fields are a spec witness".

## Main results

* `issueRelW_of_wit`, `redeemRelW_of_wit`, `issueRel_of_witR` / `issueRel_of_witB`,
  `spendRel_of_wit` / `spendRel_of_witB`, `pomRel_of_wit`: arithmetized → spec, for the five
  relations (`_witR`, `spendRel_of_wit`: spec-typed instances; `_witB`: the verifier's byte arrays).
* `hinj_moussakaIssue_of`, `hinj_moussakaRedeem`, `hinj_ratatouilleIssue`,
  `hinj_ratatouilleSpend`, and the spec-typed `hinj_ratatouilleIssue_spec`,
  `hinj_ratatouilleSpend_spec`: the injective-encoding hypothesis `hinj` of the adaptive
  soundness theorems, for families with fixed-length fields that are injective on the fields the
  encoding hashes (for redemption and spend: the keys' digests, not the keys).
-/

open Finset

namespace VoleMole.EndToEnd.SpecRel

open VoleMole.Arith VoleMole.Verifier VoleMole.Privacy

/-! ## Bits and bytes of a candidate -/

/-- The bits of committed values (`w i = 1`). -/
def bitsOf (w : ℕ → GF128) : ℕ → Bool := fun i => decide (w i = 1)

theorem gf_zero_ne_one : (0 : GF128) ≠ 1 := by decide

theorem bitsOf_eq {w : ℕ → GF128} {wb : ℕ → Bool} {N : ℕ} (h : ∀ i < N, w i = bitF (wb i))
    {i : ℕ} (hi : i < N) : bitsOf w i = wb i := by
  have e := h i hi
  cases hb : wb i <;> simp [bitsOf, e, hb, bitF]

theorem witByte_bitsOf {w : ℕ → GF128} {wb : ℕ → Bool} {N b : ℕ}
    (h : ∀ i < N, w i = bitF (wb i)) (hb : 8 * b + 8 ≤ N) :
    Keccak.witByte (bitsOf w) b = Keccak.witByte wb b :=
  Ratatouille.uint8_ext fun j hj => by
    rw [Ratatouille.witByte_bit _ _ _ hj, Ratatouille.witByte_bit _ _ _ hj,
      bitsOf_eq h (by omega)]

/-- The `n` witness bytes from byte `o`. -/
def bytesOf (wb : ℕ → Bool) (o n : ℕ) : Spec.Bytes :=
  List.ofFn fun i : Fin n => Keccak.witByte wb (o + i)

@[simp] theorem length_bytesOf (wb : ℕ → Bool) (o n : ℕ) : (bytesOf wb o n).length = n := by
  simp [bytesOf]

theorem getD_bytesOf (wb : ℕ → Bool) (o : ℕ) {n i : ℕ} (hi : i < n) :
    (bytesOf wb o n).getD i 0 = Keccak.witByte wb (o + i) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp [bytesOf]

theorem bytesOf_bitsOf {w : ℕ → GF128} {wb : ℕ → Bool} {N : ℕ}
    (h : ∀ i < N, w i = bitF (wb i)) {o n : ℕ} (hN : 8 * (o + n) ≤ N) :
    bytesOf (bitsOf w) o n = bytesOf wb o n := by
  unfold bytesOf
  congr 1
  funext i
  exact witByte_bitsOf h (by have := i.isLt; omega)

/-- The byte string of `fnOf`. -/
theorem fnOf_eq_getD (b : ByteArray) (i : ℕ) : fnOf b i = (toL b).getD i 0 := by
  rw [toL_eq, fnOf, List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_eq_getElem (by simpa using h)]
    simp [ByteArray.getElem_eq_getElem_data]
  · rw [List.getElem?_eq_none (by simp only [Array.length_toList]; exact Nat.le_of_not_lt h)]
    rfl

theorem list_ext_getD {a b : List UInt8} (hl : a.length = b.length)
    (h : ∀ i < a.length, a.getD i 0 = b.getD i 0) : a = b :=
  List.ext_getElem hl fun i h1 h2 => by
    have := h i h1
    rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

theorem toL_inj {a b : ByteArray} (h : toL a = toL b) : a = b := by
  apply ByteArray.ext
  rw [← Array.toList_inj, ← toL_eq, ← toL_eq, h]

theorem toL_append (a b : ByteArray) : toL (a ++ b) = toL a ++ toL b := by
  rw [toL_eq, toL_eq, toL_eq, ByteArray.data_append, Array.toList_append]

theorem toL_toBA (l : Spec.Bytes) : toL (toBA l) = l := by
  rw [toL_eq]; rfl

/-! ## Moussaka issuance -/

section MoussakaIssue

open VoleMole.Spec.Moussaka

/-- **The spec issuance witness of a candidate**: the decoded `nf`, `ctx_red`, `r` (witness bytes
`[32, 56)`, `[16, 32)`, `[0, 16)`), encoded by `encode_issue_witness` (with the honest committed
states of their commitment input). -/
def issueWitOf (ctxIss : Spec.Bytes) (w : ℕ → GF128) : Spec.Bytes :=
  encodeIssueWitness (bytesOf (bitsOf w) 32 24) ctxIss (bytesOf (bitsOf w) 16 16)
    (bytesOf (bitsOf w) 0 16)

/-- **Moussaka issuance, arithmetized → spec**: for `t` of 45 bytes (`COMMITMENT_BYTES = M`) and
`ctx_iss` of 16, a candidate in the arithmetized relation (`t = Com(…)` on the 45 bytes of `t`)
decodes to a witness of the spec relation, `t = Com(nf, ctx_iss, ctx_red, r)` as byte strings. -/
theorem issueRelW_of_wit (t ctxIss : ByteArray) (ht : t.size = 45) (hci : ctxIss.size = 16)
    (w : ℕ → GF128) (h : moussakaIssueWit (fun k => fnOf t k.val) (fnOf ctxIss) w) :
    Moussaka.IssueRelW ⟨toL t, toL ctxIss⟩ (issueWitOf (toL ctxIss) w) := by
  obtain ⟨wb, hb, hrel⟩ := h
  have hci' : (toL ctxIss).length = 16 := by rw [length_toL, hci]
  rw [issueWitOf, bytesOf_bitsOf hb (by decide), bytesOf_bitsOf hb (by decide),
    bytesOf_bitsOf hb (by decide)]
  refine ⟨⟨_, _, _, length_bytesOf _ _ _, length_bytesOf _ _ _, length_bytesOf _ _ _, rfl, ?_⟩,
    hci'⟩
  have hE : Arith.Moussaka.encodeComState (Arith.Moussaka.issueNf wb) (fnOf ctxIss)
      (Arith.Moussaka.issueCtxRed wb) (Arith.Moussaka.issueR wb) =
      Spec.stateOfBytes (comState (bytesOf wb 32 24) (toL ctxIss) (bytesOf wb 16 16)
        (bytesOf wb 0 16)) :=
    VoleMole.Privacy.Moussaka.encodeComState_eq _ _ _ _ (length_bytesOf _ _ _) hci'
      (length_bytesOf _ _ _) (length_bytesOf _ _ _) _ _ _ _
      (fun i hi => by rw [getD_bytesOf _ _ hi]; rfl) (fun i _ => fnOf_eq_getD _ _)
      (fun i hi => by rw [getD_bytesOf _ _ hi]; rfl) (fun i hi => by rw [getD_bytesOf _ _ hi]; rfl)
  refine list_ext_getD (by rw [length_toL, ht, length_com]) fun k hk => ?_
  rw [length_toL, ht] at hk
  have e := congrFun hrel ⟨k, hk⟩
  rw [← fnOf_eq_getD, VoleMole.Privacy.Moussaka.com_getD _ _ _ _ ⟨k, hk⟩]
  simp only at e
  rw [e, Arith.Moussaka.com, hE]

end MoussakaIssue

/-! ## Moussaka redemption -/

section MoussakaRedeem

open VoleMole.Spec VoleMole.Spec.Moussaka

/-- The selected Anchor index: the first set selector bit (`64` if none). -/
def selOf (wb : ℕ → Bool) : ℕ := (List.range 64).findIdx fun u => wb (Arith.Moussaka.selBit u)

theorem selOf_eq {wb : ℕ → Bool} {u₀ : ℕ} (hu : u₀ < 64)
    (h : ∀ u < 64, wb (Arith.Moussaka.selBit u) = decide (u = u₀)) : selOf wb = u₀ := by
  rw [selOf, List.findIdx_eq (by simpa using hu)]
  simp only [List.getElem_range]
  refine ⟨by rw [h u₀ hu]; simp, fun j hj => ?_⟩
  rw [h j (by omega)]
  simp; omega

/-- **The spec redemption witness of a candidate**: the decoded `r`, `s` (witness bytes
`[0, 16)`, `[16, 135)`) and selected index, encoded by `encode_redeem_witness`. -/
def redeemWitOf (nf ctxIss ctxRed : Spec.Bytes) (w : ℕ → GF128) : Spec.Bytes :=
  encodeRedeemWitness nf ctxIss ctxRed (bytesOf (bitsOf w) 0 16) (bytesOf (bitsOf w) 16 119)
    (selOf (bitsOf w))

/-- `UOVKey.eval` at the bytes of a candidate is the public map at its witness bytes. -/
theorem getD_eval_bytesOf (pk : UOVKey) (wb : ℕ → Bool) (o : ℕ) {k : ℕ} (hk : k < 45) :
    (pk.eval (bytesOf wb o 119)).getD k 0 =
      (UOV.publicMap 119 45 pk.map (fun i => ⟨Keccak.witByte wb (o + i)⟩) ⟨k, hk⟩).val := by
  simp only [UOVKey.eval]
  rw [List.getD_eq_getElem _ _ (by simpa using hk)]
  simp only [List.getElem_map, List.getElem_finRange]
  refine congrArg GF256.val (publicMap_congr pk.map (fun i hi => ?_) _)
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray]
  rw [← List.getD_eq_getElem?_getD, getD_bytesOf _ _ hi]

/-- **Moussaka redemption, arithmetized → spec**: for at most 64 Anchors, `nf` of 24 bytes and
contexts of 16, a candidate in the arithmetized relation decodes to a witness of the spec relation:
the selected Anchor `u` (the set selector bit) and `P_u(s) = Com(nf, ctx_iss, ctx_red, r)` as
byte strings (any `challenge_digest`). -/
theorem redeemRelW_of_wit (anchors : List UovPk) (hn : anchors.length ≤ 64)
    (nf ctxIss ctxRed cd : ByteArray) (hnf : nf.size = 24) (hci : ctxIss.size = 16)
    (hcr : ctxRed.size = 16) (w : ℕ → GF128)
    (h : moussakaRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf) (fnOf ctxIss)
      (fnOf ctxRed) w) :
    Moussaka.RedeemRelW ⟨anchors.map UovPk.toSpec, toL nf, toL ctxIss, toL ctxRed, toL cd⟩
      (redeemWitOf (toL nf) (toL ctxIss) (toL ctxRed) w) := by
  obtain ⟨wb, hb, u₀, hsel, hrel⟩ := h
  obtain ⟨hu, hk⟩ := (Arith.Moussaka.redeemRel_gf256_iff _ _ _ _ _ wb u₀).1 hrel
  have hu' : u₀ < anchors.length := by simpa using hu
  have hnf' : (toL nf).length = 24 := by rw [length_toL, hnf]
  have hci' : (toL ctxIss).length = 16 := by rw [length_toL, hci]
  have hcr' : (toL ctxRed).length = 16 := by rw [length_toL, hcr]
  have hs : selOf (bitsOf w) = u₀ := selOf_eq (by omega) fun u hu64 => by
    rw [bitsOf_eq hb (by simp only [Arith.Moussaka.selBit, Arith.Moussaka.redeemOffB,
      Arith.Moussaka.redeemWitnessBits]; omega)]
    exact hsel u hu64
  rw [redeemWitOf, hs, bytesOf_bitsOf hb (by decide), bytesOf_bitsOf hb (by decide)]
  refine ⟨⟨_, _, u₀, (anchors.map UovPk.toSpec)[u₀]'(by simpa using hu'), length_bytesOf _ _ _,
    length_bytesOf _ _ _, List.getElem?_eq_getElem _, rfl, ?_⟩, by simpa using hn, hnf', hci', hcr'⟩
  have hE : Arith.Moussaka.encodeComState (fnOf nf) (fnOf ctxIss) (fnOf ctxRed)
      (Arith.Moussaka.redeemR wb) =
      stateOfBytes (comState (toL nf) (toL ctxIss) (toL ctxRed) (bytesOf wb 0 16)) :=
    VoleMole.Privacy.Moussaka.encodeComState_eq _ _ _ _ hnf' hci' hcr' (length_bytesOf _ _ _)
      _ _ _ _ (fun i _ => fnOf_eq_getD _ _) (fun i _ => fnOf_eq_getD _ _)
      (fun i _ => fnOf_eq_getD _ _) (fun i hi => by rw [getD_bytesOf _ _ hi]; rfl)
  refine list_ext_getD (by rw [length_eval, length_com]) fun k hk' => ?_
  rw [length_eval] at hk'
  rw [getD_eval_bytesOf _ _ _ hk', VoleMole.Privacy.Moussaka.com_getD _ _ _ _ ⟨k, hk'⟩, ← hE]
  have e := hk ⟨k, hk'⟩
  simp only [List.getElem_map] at e ⊢
  rw [show (16 : ℕ) = Arith.Moussaka.redeemOffS from rfl]
  exact e

end MoussakaRedeem

/-! ## Ratatouille issuance -/

section RatatouilleIssue

open VoleMole.Spec.Ratatouille

/-- **The spec issuance witness of a candidate**: `nf` at witness byte 16, `r` at 0. -/
def issueWitOfR (w : ℕ → GF128) : IssueWitness :=
  ⟨Vector.ofFn fun i : Fin 24 => Keccak.witByte (bitsOf w) (16 + i),
    Vector.ofFn fun i : Fin 16 => Keccak.witByte (bitsOf w) (0 + i)⟩

theorem fn_ofFn {n : ℕ} (f : Fin n → UInt8) {i : ℕ} (hi : i < n) :
    Bytes.fn (Vector.ofFn f : Spec.Ratatouille.Bytes n) i = f ⟨i, hi⟩ := by
  simp [Bytes.fn, hi]

theorem get_eq_fn {n : ℕ} (v : Spec.Ratatouille.Bytes n) {i : ℕ} (hi : i < n) :
    v[i] = Bytes.fn v i := by
  simp [Bytes.fn, hi]

/-- **Ratatouille issuance, arithmetized → spec** (well-formedness is in the spec types): a
candidate in the arithmetized relation for the statement of the spec instance `x` decodes to a
witness of `R_iss`, `c = Com(nf, ctx, T_init, r)`. -/
theorem issueRel_of_wit_gen (x : IssueInstance) (fc fctx : ℕ → UInt8)
    (hc : ∀ i < 32, fc i = Bytes.fn x.c i) (hctx : ∀ i < 16, fctx i = Bytes.fn x.ctx i)
    (w : ℕ → GF128) (h : ratatouilleIssueWit fc x.tInit.toNat fctx w) :
    IssueRel x (issueWitOfR w) := by
  obtain ⟨wb, hb, hrel⟩ := h
  refine Vector.ext fun k hk => ?_
  rw [get_eq_fn _ hk, ← hc k hk, hrel k hk]
  simp only [com, Vector.getElem_ofFn, Arith.Ratatouille.commit]
  rw [Ratatouille.comState_congr _ (fun i hi => ?_) hctx (fun i hi => ?_)]
  · rw [issueWitOfR, fn_ofFn _ hi, witByte_bitsOf hb (by simp only [Arith.Ratatouille.issueWitnessBytes]; omega)]
    rfl
  · rw [issueWitOfR, fn_ofFn _ hi, witByte_bitsOf hb (by simp only [Arith.Ratatouille.issueWitnessBytes]; omega)]
    rfl

/-- **Ratatouille issuance, arithmetized → spec**, for the statement of a spec instance `x`
(well-formedness is in the spec types). -/
theorem issueRel_of_witR (x : IssueInstance) (w : ℕ → GF128)
    (h : ratatouilleIssueWit (fnOf (Ratatouille.bOf x.c)) x.tInit.toNat
      (fnOf (Ratatouille.bOf x.ctx)) w) :
    IssueRel x (issueWitOfR w) :=
  issueRel_of_wit_gen x _ _ (fun i _ => by rw [Ratatouille.fnOf_bOf])
    (fun i _ => by rw [Ratatouille.fnOf_bOf]) w h

/-- The first `n` bytes of a byte array, as a spec byte vector (zero-padded). -/
def bytesVec (n : ℕ) (b : ByteArray) : Spec.Ratatouille.Bytes n := Vector.ofFn fun i : Fin n => fnOf b i

theorem fn_bytesVec (n : ℕ) (b : ByteArray) {i : ℕ} (hi : i < n) :
    Bytes.fn (bytesVec n b) i = fnOf b i := fn_ofFn _ hi

/-- For a byte array of length `n`, `bytesVec n` is a section of `bOf`. -/
theorem bOf_bytesVec {n : ℕ} {b : ByteArray} (hb : b.size = n) :
    Ratatouille.bOf (bytesVec n b) = b := by
  apply toL_inj
  rw [Ratatouille.bOf, toL_toBA]
  refine list_ext_getD (by simp [length_toL, hb]) fun i hi => ?_
  simp only [Vector.length_toList] at hi
  rw [← fnOf_eq_getD, Ratatouille.getD_toList_fn, fn_bytesVec _ _ hi]

/-- The spec issuance instance of the verifier's statement `ratatouilleIssue c t_init ctx_iss`:
`c` and `ctx_iss` as 32- and 16-byte vectors (`bOf_bytesVec`: these are `c` and `ctx_iss` when
they have those lengths), `t_init` as a `UInt64`. -/
def issueInstOf (c : ByteArray) (tInit : ℕ) (ctx : ByteArray) : IssueInstance :=
  ⟨bytesVec 32 c, UInt64.ofNat tInit, bytesVec 16 ctx⟩

theorem issueInstOf_tInit (c : ByteArray) (tInit : ℕ) (ctx : ByteArray) :
    (issueInstOf c tInit ctx).tInit = UInt64.ofNat tInit := rfl

/-- **Ratatouille issuance, arithmetized → spec**, for the verifier's byte-array statement with
`t_init < 2⁶⁴`. -/
theorem issueRel_of_witB (c : ByteArray) (tInit : ℕ) (ctx : ByteArray) (ht : tInit < 2 ^ 64)
    (w : ℕ → GF128) (h : ratatouilleIssueWit (fnOf c) tInit (fnOf ctx) w) :
    IssueRel (issueInstOf c tInit ctx) (issueWitOfR w) := by
  have e : (UInt64.ofNat tInit).toNat = tInit := UInt64.toNat_ofNat_of_lt' ht
  have h' : ratatouilleIssueWit (fnOf c) (issueInstOf c tInit ctx).tInit.toNat (fnOf ctx) w := by
    rw [issueInstOf_tInit, e]; exact h
  exact issueRel_of_wit_gen (issueInstOf c tInit ctx) (fnOf c) (fnOf ctx) (fun i hi => (fn_bytesVec _ _ hi).symm)
    (fun i hi => (fn_bytesVec _ _ hi).symm) w h'

end RatatouilleIssue

/-! ## Ratatouille spend -/

section RatatouilleSpend

open VoleMole.Spec.Ratatouille

/-- **The spec spend witness of a candidate**: `t`, `x`, `t'` the credit values at witness bytes
16, 24, 88; `r`, `nf'`, `r'`, `s` the bytes at 0, 64, 96, 112. -/
def spendWitOf (w : ℕ → GF128) : SpendWitness where
  t := UInt64.ofNat (Arith.Ratatouille.creditAt (bitsOf w) 16)
  r := Vector.ofFn fun i : Fin 16 => Keccak.witByte (bitsOf w) (0 + i)
  x := UInt64.ofNat (Arith.Ratatouille.creditAt (bitsOf w) 24)
  s := Vector.ofFn fun i : Fin 119 => Keccak.witByte (bitsOf w) (112 + i)
  nf' := Vector.ofFn fun i : Fin 24 => Keccak.witByte (bitsOf w) (64 + i)
  t' := UInt64.ofNat (Arith.Ratatouille.creditAt (bitsOf w) 88)
  r' := Vector.ofFn fun i : Fin 16 => Keccak.witByte (bitsOf w) (96 + i)

/-- `encode_tag_state` reads the commitment on its 32 bytes only. -/
theorem tagState_congr {c c' : ℕ → UInt8} (x : ℕ) (h : ∀ i < 32, c i = c' i) :
    Arith.Ratatouille.tagState c x = Arith.Ratatouille.tagState c' x := by
  apply Vector.ext
  intro k hk
  simp only [Arith.Ratatouille.tagState, Vector.getElem_ofFn]
  split_ifs <;> first | rfl | exact h _ (by omega)

theorem creditAt_bitsOf {w : ℕ → GF128} {wb : ℕ → Bool}
    (hb : ∀ i < 8 * Arith.Ratatouille.spendWitnessBytes, w i = bitF (wb i)) {o : ℕ}
    (ho : o ≤ 88) : Arith.Ratatouille.creditAt (bitsOf w) o = Arith.Ratatouille.creditAt wb o :=
  Ratatouille.val_congr fun i hi =>
    bitsOf_eq hb (by simp only [Arith.Ratatouille.spendWitnessBytes]; omega)

theorem toNat_ofNat_creditAt (wb : ℕ → Bool) (o : ℕ) :
    (UInt64.ofNat (Arith.Ratatouille.creditAt wb o)).toNat = Arith.Ratatouille.creditAt wb o :=
  UInt64.toNat_ofNat_of_lt' (Arith.Ratatouille.creditAt_lt wb o)

/-- **Ratatouille spend, arithmetized → spec** (well-formedness is in the spec types; the
verifier's key `pk` has the instance's public map): a candidate in the arithmetized relation for
the statement of `x` decodes to a witness of `R_spend` (V1–V3; V4 by the types). -/
theorem spendRel_of_wit_gen (x : SpendInstance) (pk : ℕ → GF256) (hpk : pk = x.pk)
    (fnf fcn fctx : ℕ → UInt8) (hnf : ∀ i < 24, fnf i = Bytes.fn x.nf i)
    (hcn : ∀ i < 32, fcn i = Bytes.fn x.cNext i) (hctx : ∀ i < 16, fctx i = Bytes.fn x.ctx i)
    (w : ℕ → GF128) (h : ratatouilleSpendWit GF256.ofBits pk fnf x.d.toNat fcn fctx w) :
    SpendRel x (spendWitOf w) := by
  obtain ⟨wb, hb, hrel⟩ := h
  rw [Arith.Ratatouille.spendRelOf_gf256_iff, hpk] at hrel
  obtain ⟨h1, h2, h3, -, -, -, -⟩ := hrel
  have hC : ∀ (nf : ℕ → UInt8) t (r : ℕ → UInt8), (∀ i < 24, nf i = Bytes.fn x.nf i) →
      Arith.Ratatouille.commit nf fctx t r = Arith.Ratatouille.commit (Bytes.fn x.nf) (Bytes.fn x.ctx) t r :=
    fun nf t r hn => by
      simp only [Arith.Ratatouille.commit]
      rw [Ratatouille.comState_congr t hn hctx (fun _ _ => rfl)]
  have hC2 : ∀ (nf : ℕ → UInt8) t (r : ℕ → UInt8),
      Arith.Ratatouille.commit nf fctx t r = Arith.Ratatouille.commit nf (Bytes.fn x.ctx) t r :=
    fun nf t r => by
      simp only [Arith.Ratatouille.commit]
      rw [Ratatouille.comState_congr t (fun _ _ => rfl) hctx (fun _ _ => rfl)]
  rw [hC _ _ _ hnf] at h1
  replace h2 : ∀ k < 32, Bytes.fn x.cNext k = Arith.Ratatouille.commit
      (Arith.Ratatouille.bytesAt wb 64) (Bytes.fn x.ctx) (Arith.Ratatouille.creditAt wb 88)
      (Arith.Ratatouille.bytesAt wb 96) k := fun k hk => by
    rw [← hcn k hk, h2 k hk, hC2]
  have hB : ∀ {o n : ℕ}, o + n ≤ 847 → ∀ i < n,
      Keccak.witByte (bitsOf w) (o + i) = Keccak.witByte wb (o + i) := fun hon i hi =>
    witByte_bitsOf hb (by simp only [Arith.Ratatouille.spendWitnessBytes]; omega)
  have hcom : ∀ (nf : Nullifier) (t : ℕ) (r : Opening) (nf' : ℕ → UInt8) (r' : ℕ → UInt8),
      (∀ i < 24, nf.fn i = nf' i) → (∀ i < 16, r.fn i = r' i) → ∀ k,
      Arith.Ratatouille.commit nf.fn x.ctx.fn t r.fn k =
        Arith.Ratatouille.commit nf' x.ctx.fn t r' k := fun nf t r nf' r' hn hr k => by
    simp only [Arith.Ratatouille.commit]
    rw [Ratatouille.comState_congr t hn (fun _ _ => rfl) hr]
  have ht : (spendWitOf w).t.toNat = Arith.Ratatouille.creditAt wb 16 := by
    show (UInt64.ofNat (Arith.Ratatouille.creditAt (bitsOf w) 16)).toNat = _
    rw [toNat_ofNat_creditAt, creditAt_bitsOf hb (by norm_num)]
  have hx : (spendWitOf w).x.toNat = Arith.Ratatouille.creditAt wb 24 := by
    show (UInt64.ofNat (Arith.Ratatouille.creditAt (bitsOf w) 24)).toNat = _
    rw [toNat_ofNat_creditAt, creditAt_bitsOf hb (by norm_num)]
  have ht' : (spendWitOf w).t'.toNat = Arith.Ratatouille.creditAt wb 88 := by
    show (UInt64.ofNat (Arith.Ratatouille.creditAt (bitsOf w) 88)).toNat = _
    rw [toNat_ofNat_creditAt, creditAt_bitsOf hb (by norm_num)]
  have hr : ∀ j < 16, Bytes.fn (spendWitOf w).r j = Arith.Ratatouille.bytesAt wb 0 j :=
    fun j hj => by
      show Bytes.fn (Vector.ofFn _) j = _
      rw [fn_ofFn _ hj, hB (by norm_num) j hj]; rfl
  have hr' : ∀ j < 16, Bytes.fn (spendWitOf w).r' j = Arith.Ratatouille.bytesAt wb 96 j :=
    fun j hj => by
      show Bytes.fn (Vector.ofFn _) j = _
      rw [fn_ofFn _ hj, hB (by norm_num) j hj]; rfl
  have hnf' : ∀ j < 24, Bytes.fn (spendWitOf w).nf' j = Arith.Ratatouille.bytesAt wb 64 j :=
    fun j hj => by
      show Bytes.fn (Vector.ofFn _) j = _
      rw [fn_ofFn _ hj, hB (by norm_num) j hj]; rfl
  have hs : ∀ j < 119, Bytes.fn (spendWitOf w).s j = Keccak.witByte wb (112 + j) :=
    fun j hj => by
      show Bytes.fn (Vector.ofFn _) j = _
      rw [fn_ofFn _ hj, hB (by norm_num) j hj]
  refine ⟨Vector.ext fun k hk => ?_, Vector.ext fun k hk => ?_, ?_⟩
  · simp only [uovEval, tag, Vector.getElem_ofFn]
    rw [publicMap_congr (N := 119) x.pk (σ' := fun i => ⟨Keccak.witByte wb (112 + i)⟩)
      (fun i hi => by rw [hs i hi])]
    have e1 := h1 ⟨k, hk⟩
    simp only [Arith.Ratatouille.uovN, Arith.Ratatouille.uovM] at e1
    have hc : ∀ i < 32, Bytes.fn (com x.nf x.ctx (spendWitOf w).t (spendWitOf w).r) i =
        Arith.Ratatouille.commit (Bytes.fn x.nf) (Bytes.fn x.ctx)
          (Arith.Ratatouille.creditAt wb 16) (Arith.Ratatouille.bytesAt wb 0) i := fun i hi => by
      rw [← get_eq_fn _ hi]
      simp only [com, Vector.getElem_ofFn]
      rw [ht]
      exact hcom _ _ _ _ _ (fun _ _ => rfl) hr i
    rw [e1, hx, tagState_congr _ hc]
  · rw [get_eq_fn _ hk, h2 k hk]
    simp only [com, Vector.getElem_ofFn]
    rw [ht']
    exact (hcom _ _ _ _ _ hnf' hr' k).symm
  · rw [ht, hx, ht', h3]

/-- **Ratatouille spend, arithmetized → spec**, for the statement of a spec instance `x` (well-
formedness is in the spec types; the verifier's key `pk` has the instance's public map). -/
theorem spendRel_of_wit (x : SpendInstance) (pk : UovPk) (hpk : pk.map = x.pk) (w : ℕ → GF128)
    (h : ratatouilleSpendWit GF256.ofBits pk.map (fnOf (Ratatouille.bOf x.nf)) x.d.toNat
      (fnOf (Ratatouille.bOf x.cNext)) (fnOf (Ratatouille.bOf x.ctx)) w) :
    SpendRel x (spendWitOf w) :=
  spendRel_of_wit_gen x pk.map hpk _ _ _ (fun i _ => by rw [Ratatouille.fnOf_bOf])
    (fun i _ => by rw [Ratatouille.fnOf_bOf]) (fun i _ => by rw [Ratatouille.fnOf_bOf]) w h

/-- The spec spend instance of the verifier's statement `ratatouilleSpend pk nf d c_next ctx_iss`:
the key's public map, `nf`, `c_next`, `ctx_iss` as 24-, 32-, 16-byte vectors (`bOf_bytesVec`), `d`
as a `UInt64`. -/
def spendInstOf (pk : UovPk) (nf : ByteArray) (d : ℕ) (cNext ctx : ByteArray) : SpendInstance :=
  ⟨pk.map, bytesVec 24 nf, UInt64.ofNat d, bytesVec 32 cNext, bytesVec 16 ctx⟩

theorem spendInstOf_d (pk : UovPk) (nf : ByteArray) (d : ℕ) (cNext ctx : ByteArray) :
    (spendInstOf pk nf d cNext ctx).d = UInt64.ofNat d := rfl

/-- **Ratatouille spend, arithmetized → spec**, for the verifier's byte-array statement
(`d < 2⁶⁴`, as the soundness theorems assume). -/
theorem spendRel_of_witB (pk : UovPk) (nf : ByteArray) (d : ℕ) (hd : d < 2 ^ 64)
    (cNext ctx : ByteArray) (w : ℕ → GF128)
    (h : ratatouilleSpendWit GF256.ofBits pk.map (fnOf nf) d (fnOf cNext) (fnOf ctx) w) :
    SpendRel (spendInstOf pk nf d cNext ctx) (spendWitOf w) := by
  have e : (UInt64.ofNat d).toNat = d := UInt64.toNat_ofNat_of_lt' hd
  have h' : ratatouilleSpendWit GF256.ofBits pk.map (fnOf nf)
      (spendInstOf pk nf d cNext ctx).d.toNat (fnOf cNext) (fnOf ctx) w := by
    rw [spendInstOf_d, e]; exact h
  exact spendRel_of_wit_gen (spendInstOf pk nf d cNext ctx) pk.map rfl (fnOf nf) (fnOf cNext) (fnOf ctx)
    (fun i hi => (fn_bytesVec _ _ hi).symm) (fun i hi => (fn_bytesVec _ _ hi).symm)
    (fun i hi => (fn_bytesVec _ _ hi).symm) w h'

end RatatouilleSpend

/-! ## PomFRIT redemption -/

section PomFRIT

open VoleMole.Spec

/-- **PomFRIT's redemption relation on byte strings**, `R((pk, h), (r, s)) ⇔ P(s) = h ⊕ r` with
`r`, `h` of `M = 45` bytes and `s` of `N = 119` (the relation of `Spec.PomFRIT.Correct.complete`;
`pomfrit.cpp:174-175`). -/
def PomRel (pk : UOVKey) (h r s : Spec.Bytes) : Prop :=
  r.length = uovM ∧ h.length = uovM ∧ s.length = uovN ∧ pk.eval s = xorBytes h r

theorem size_pomfritTarget (p : Params) (dig chal1 sig msg : ByteArray) :
    (pomfritTarget p dig chal1 sig msg).size = 45 := by
  rw [pomfritTarget, size_toBA, length_shake128B]

/-- **PomFRIT redemption, arithmetized → spec**: for a 45-byte target `h` (every
`pomfritTarget`, `size_pomfritTarget`), a candidate in the arithmetized relation decodes to
`(r, s)` (witness bytes `[0, 45)`, `[45, 164)`) with `P(s) = h ⊕ r` as byte strings. -/
theorem pomRel_of_wit (pk : UovPk) (h : ByteArray) (hh : h.size = 45) (w : ℕ → GF128)
    (hw : pomfritWit GF256.ofBits 119 45 pk.map (fun k => ⟨fnOf h k.val⟩) w) :
    PomRel pk.toSpec (toL h) (bytesOf (bitsOf w) 0 45) (bytesOf (bitsOf w) 45 119) := by
  obtain ⟨wb, hb, hr⟩ := hw
  have e := (PomFRIT.pomfritRel_gf256_iff 119 45 pk.map _ wb).1 hr
  have hh' : (toL h).length = 45 := by rw [length_toL, hh]
  rw [bytesOf_bitsOf hb (by decide), bytesOf_bitsOf hb (by decide)]
  refine ⟨length_bytesOf _ _ _, hh', length_bytesOf _ _ _, ?_⟩
  refine list_ext_getD (by rw [length_eval, length_xorBytes, hh', length_bytesOf]; rfl)
    fun k hk => ?_
  rw [length_eval] at hk
  rw [getD_eval_bytesOf _ _ _ hk, xorBytes, List.getD_eq_getElem _ _ (by simp [hh']; omega),
    List.getElem_zipWith]
  refine (e ⟨k, hk⟩).trans ?_
  rw [← List.getD_eq_getElem _ 0, ← List.getD_eq_getElem _ 0, getD_bytesOf _ _ hk,
    ← fnOf_eq_getD]
  rfl

end PomFRIT

/-! ## Injective instance encodings (`hinj`) -/

section Hinj

open VoleMole.Spec

/-- `le64` is injective below `2⁶⁴`. -/
theorem le64_inj {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : le64 a = le64 b) : a = b := by
  have hd := congrArg ByteArray.data h
  simp only [le64] at hd
  have hbyte : ∀ i < 8, (a / 2 ^ (8 * i)) % 256 = (b / 2 ^ (8 * i)) % 256 := fun i hi => by
    have := congrArg (fun A : Array UInt8 => (A[i]?.getD 0).toNat) hd
    simpa [Array.getElem?_map, Array.getElem?_range, hi, Nat.toUInt8, UInt8.toNat_ofNat] using this
  refine Nat.eq_of_testBit_eq fun j => ?_
  by_cases hj : j < 64
  · have e := congrArg (fun n => n.testBit (j % 8)) (hbyte (j / 8) (by omega))
    simp only [show (256 : ℕ) = 2 ^ 8 by norm_num, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
      show j % 8 < 8 from Nat.mod_lt _ (by norm_num), decide_true, Bool.true_and] at e
    rwa [show j % 8 + 8 * (j / 8) = j by omega] at e
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem size_le64 (v : ℕ) : (le64 v).size = 8 := by
  simp [le64, ByteArray.size]

theorem toBA_inj {a b : Spec.Bytes} (h : toBA a = toBA b) : a = b := by
  rw [← toL_toBA a, ← toL_toBA b, h]

/-- **`hinj` for Moussaka issuance families with `t` of fixed length** (the proof of
`Audit.hinj_moussakaIssue`). -/
theorem hinj_moussakaIssue_of {ι : Type} (inst : ι → ByteArray × ByteArray) (lr : Bool) (n : ℕ)
    (hlen : ∀ s, (inst s).1.size = n) (hi : Function.Injective inst) :
    Function.Injective fun s =>
      (moussakaIssue (inst s).1 (inst s).2 lr).instEnc ByteArray.empty := by
  intro s s' h
  simp only [moussakaIssue] at h
  have h' := Moussaka.issueEncode_inj (x := ⟨toL (inst s).1, toL (inst s).2⟩)
    (y := ⟨toL (inst s').1, toL (inst s').2⟩) (by simp [length_toL, hlen]) (toBA_inj h)
  exact hi (Prod.ext (toL_inj h'.1) (toL_inj h'.2))

/-- **`hinj` for Moussaka redemption families**: Anchor keys with 32-byte digests, fewer than
256 Anchors, `nf` and the two contexts of fixed lengths, and the family injective on what the
encoding hashes, `(digests of the Anchors, nf, ctx_iss, ctx_red, challenge_digest)`
(`Spec.Moussaka.redeemEncode_inj`). -/
theorem hinj_moussakaRedeem {ι : Type} (anc : ι → List UovPk) (nf ctxIss ctxRed cd : ι → ByteArray)
    (lr : Bool) (hdig : ∀ s, ∀ pk ∈ anc s, pk.digest.size = 32) (hn : ∀ s, (anc s).length < 256)
    (nN nI nR : ℕ) (hnf : ∀ s, (nf s).size = nN) (hci : ∀ s, (ctxIss s).size = nI)
    (hcr : ∀ s, (ctxRed s).size = nR)
    (hi : Function.Injective fun s =>
      ((anc s).map UovPk.digest, nf s, ctxIss s, ctxRed s, cd s)) :
    Function.Injective fun s =>
      (moussakaRedeem (anc s) (nf s) (ctxIss s) (ctxRed s) (cd s) lr).instEnc ByteArray.empty := by
  intro s s' h
  simp only [moussakaRedeem] at h
  have hd : ∀ s, ∀ pk ∈ (anc s).map UovPk.toSpec, pk.digest.length = digestBytes := by
    intro s pk hpk
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hpk
    simp [UovPk.toSpec, length_toL, hdig s p hp]
  obtain ⟨h1, h2, h3, h4, h5⟩ := Moussaka.redeemEncode_inj (hd s) (hd s') (by simpa using hn s)
    (by simpa using hn s') (by simp [length_toL, hnf]) (by simp [length_toL, hci])
    (by simp [length_toL, hcr]) (toBA_inj h)
  have hdg : (anc s).map UovPk.digest = (anc s').map UovPk.digest := by
    have hL : Function.Injective (List.map toL) :=
      List.map_injective_iff.2 fun _ _ => toL_inj
    apply hL
    simpa [List.map_map, Function.comp_def, UovPk.toSpec] using h1
  exact hi (by simp only [hdg, toL_inj h2, toL_inj h3, toL_inj h4, toL_inj h5])

/-- **`hinj` for Ratatouille issuance families**: `c` of fixed length, `t_init < 2⁶⁴`, the family
injective. -/
theorem hinj_ratatouilleIssue {ι : Type} (inst : ι → ByteArray × ℕ × ByteArray) (lr : Bool)
    (n : ℕ) (hc : ∀ s, (inst s).1.size = n) (ht : ∀ s, (inst s).2.1 < 2 ^ 64)
    (hi : Function.Injective inst) :
    Function.Injective fun s =>
      (ratatouilleIssue (inst s).1 (inst s).2.1 (inst s).2.2 lr).instEnc ByteArray.empty := by
  intro s s' h
  simp only [ratatouilleIssue] at h
  have h' := congrArg toL h
  simp only [toL_append, List.append_assoc] at h'
  obtain ⟨e1, h'⟩ := concat_inj h' (by simp [length_toL, hc])
  obtain ⟨e2, e3⟩ := concat_inj h' (by simp [length_toL, size_le64])
  exact hi (Prod.ext (toL_inj e1)
    (Prod.ext (le64_inj (ht s) (ht s') (toL_inj e2)) (toL_inj e3)))

/-- **`hinj` for Ratatouille spend families**: digest, `nf` and `c_next` of fixed lengths,
`d < 2⁶⁴`, the family injective on what the encoding hashes,
`(dig(pk), nf, d, c_next, ctx_iss)`. -/
theorem hinj_ratatouilleSpend {ι : Type} (pk : ι → UovPk) (nf : ι → ByteArray) (d : ι → ℕ)
    (cNext ctxIss : ι → ByteArray) (lr : Bool) (nD nN nC : ℕ) (hdig : ∀ s, (pk s).digest.size = nD)
    (hnf : ∀ s, (nf s).size = nN) (hd : ∀ s, d s < 2 ^ 64) (hcn : ∀ s, (cNext s).size = nC)
    (hi : Function.Injective fun s => ((pk s).digest, nf s, d s, cNext s, ctxIss s)) :
    Function.Injective fun s =>
      (ratatouilleSpend (pk s) (nf s) (d s) (cNext s) (ctxIss s) lr).instEnc ByteArray.empty := by
  intro s s' h
  simp only [ratatouilleSpend] at h
  have h' := congrArg toL h
  simp only [toL_append, List.append_assoc] at h'
  obtain ⟨e1, h'⟩ := concat_inj h' (by simp [length_toL, hdig])
  obtain ⟨e2, h'⟩ := concat_inj h' (by simp [length_toL, hnf])
  obtain ⟨e3, h'⟩ := concat_inj h' (by simp [length_toL, size_le64])
  obtain ⟨e4, e5⟩ := concat_inj h' (by simp [length_toL, hcn])
  exact hi (by
    simp only [toL_inj e1, toL_inj e2, le64_inj (hd s) (hd s') (toL_inj e3), toL_inj e4,
      toL_inj e5])

theorem bOf_inj {n : ℕ} {a b : Spec.Ratatouille.Bytes n} (h : Ratatouille.bOf a = Ratatouille.bOf b) :
    a = b :=
  Vector.toList_inj.1 (toBA_inj h)

/-- `hinj` for a family of spec issuance instances: any injective family. -/
theorem hinj_ratatouilleIssue_spec {ι : Type} (x : ι → Spec.Ratatouille.IssueInstance) (lr : Bool)
    (hi : Function.Injective x) :
    Function.Injective fun s =>
      (ratatouilleIssue (Ratatouille.bOf (x s).c) (x s).tInit.toNat (Ratatouille.bOf (x s).ctx)
        lr).instEnc ByteArray.empty :=
  hinj_ratatouilleIssue (fun s => (Ratatouille.bOf (x s).c, (x s).tInit.toNat,
      Ratatouille.bOf (x s).ctx)) lr 32
    (fun s => by simp [Ratatouille.bOf, size_toBA]) (fun s => (x s).tInit.toNat_lt)
    (fun s s' h => by
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      exact hi (by
        cases hs : x s; cases hs' : x s'
        rw [hs, hs'] at h1 h2 h3
        simp only at h1 h2 h3
        rw [bOf_inj h1, bOf_inj h3, UInt64.toNat_inj.1 h2]))

/-- `hinj` for a family of spec spend instances with keys `pk s` of 32-byte digests: injective on
`(dig(pk), nf, d, c_next, ctx)`. -/
theorem hinj_ratatouilleSpend_spec {ι : Type} (x : ι → Spec.Ratatouille.SpendInstance)
    (pk : ι → UovPk) (lr : Bool) (hdig : ∀ s, (pk s).digest.size = 32)
    (hi : Function.Injective fun s => ((pk s).digest, (x s).nf, (x s).d, (x s).cNext, (x s).ctx)) :
    Function.Injective fun s =>
      (ratatouilleSpend (pk s) (Ratatouille.bOf (x s).nf) (x s).d.toNat
        (Ratatouille.bOf (x s).cNext) (Ratatouille.bOf (x s).ctx) lr).instEnc ByteArray.empty :=
  hinj_ratatouilleSpend pk (fun s => Ratatouille.bOf (x s).nf) (fun s => (x s).d.toNat)
    (fun s => Ratatouille.bOf (x s).cNext) (fun s => Ratatouille.bOf (x s).ctx) lr 32 24 32 hdig
    (fun s => by simp [Ratatouille.bOf, size_toBA]) (fun s => (x s).d.toNat_lt)
    (fun s => by simp [Ratatouille.bOf, size_toBA])
    (fun s s' h => by
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      exact hi (by
        simp only [h1, bOf_inj h2, UInt64.toNat_inj.1 h3, bOf_inj h4, bOf_inj h5]))

end Hinj

end VoleMole.EndToEnd.SpecRel
