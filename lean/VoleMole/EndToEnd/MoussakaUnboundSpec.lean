import VoleMole.EndToEnd.SpecRelations
import VoleMole.Prob.MoussakaUnbound

/-!
# The unbound Moussaka relations: from the arithmetized relations back to the spec relations

`EndToEnd/SpecRelations.lean` for the two unbound relations: an extracted candidate in the
arithmetized relation (`moussakaUnboundIssueWit`, `moussakaUnboundRedeemWit`,
`EndToEnd/MoussakaUnbound.lean`) decodes to a witness of the byte-level spec relation
(`Spec.MoussakaUnbound.IssueRel`, `RedeemRel`), so the bounds of `ROM/MoussakaUnbound*.lean` hold
for the spec relations too (`ROM/MoussakaUnboundSpec.lean`).

| relation | decoded witness | well-formedness |
| --- | --- | --- |
| unbound issue | `uIssueWitOf`: `nf_key`, `r` at witness bytes 16, 0, re-encoded by `encodeIssueWitness` (states recomputed) | `|t| = 45` |
| unbound redeem | `uRedeemWitOf`: `nf_key`, `r`, `s` at 16, 0, 32 and the selected index, re-encoded by `encodeRedeemWitness` | `|anchors| ≤ 64`, `|nf| = 24` |

Unlike the bound relations no context length is needed: the spec relations read `ctx_iss`,
`ctx_red` through `fn` (zero beyond the end), as the arithmetized ones read them through `fnOf`.

The injective-encoding hypothesis `hinj` of the adaptive theorems: `hinj_unboundIssue` (`t` of
fixed length, the C++ encoding `t ‖ ctx_iss`), `hinj_unboundRedeem` (the bound encoding
`hash_redeem_instance`, as `hinj_moussakaRedeem`), for any family of statements whose instance
encodings are these (e.g. `Unbound.refIssue`, `Unbound.refRedeem`).
-/

open Finset

namespace VoleMole.EndToEnd.SpecRel

open VoleMole.Arith VoleMole.Verifier VoleMole.Privacy

/-! ## The Keccak inputs read 16 bytes of each field -/

theorem encodeUnboundComState_congr {k ctxIss r k' ctxIss' r' : ℕ → UInt8}
    (hk : ∀ i < 16, k i = k' i) (hc : ∀ i < 16, ctxIss i = ctxIss' i)
    (hr : ∀ i < 16, r i = r' i) :
    MoussakaUnbound.encodeUnboundComState k ctxIss r =
      MoussakaUnbound.encodeUnboundComState k' ctxIss' r' := by
  unfold MoussakaUnbound.encodeUnboundComState
  congr 1
  funext i
  split_ifs
  · rfl
  · exact hr _ (by omega)
  · rfl
  · exact hc _ (by omega)
  · exact hk _ (by omega)
  · rfl

theorem encodeDeriveState_congr {k ctxRed k' ctxRed' : ℕ → UInt8}
    (hk : ∀ i < 16, k i = k' i) (hc : ∀ i < 16, ctxRed i = ctxRed' i) :
    MoussakaUnbound.encodeDeriveState k ctxRed = MoussakaUnbound.encodeDeriveState k' ctxRed' := by
  unfold MoussakaUnbound.encodeDeriveState
  congr 1
  funext i
  split_ifs
  · rfl
  · exact hk _ (by omega)
  · rfl
  · exact hc _ (by omega)
  · rfl

theorem ucom_congr {k ctxIss r k' ctxIss' r' : ℕ → UInt8}
    (hk : ∀ i < 16, k i = k' i) (hc : ∀ i < 16, ctxIss i = ctxIss' i)
    (hr : ∀ i < 16, r i = r' i) :
    MoussakaUnbound.ucom k ctxIss r = MoussakaUnbound.ucom k' ctxIss' r' := by
  unfold MoussakaUnbound.ucom
  rw [encodeUnboundComState_congr hk hc hr]

theorem derive_congr {k ctxRed k' ctxRed' : ℕ → UInt8}
    (hk : ∀ i < 16, k i = k' i) (hc : ∀ i < 16, ctxRed i = ctxRed' i) :
    MoussakaUnbound.derive k ctxRed = MoussakaUnbound.derive k' ctxRed' := by
  unfold MoussakaUnbound.derive
  rw [encodeDeriveState_congr hk hc]

/-- `fnOf b` is the spec's `fn` of its bytes. -/
theorem fnOf_eq_fn (b : ByteArray) : fnOf b = Spec.MoussakaUnbound.fn (toL b) :=
  funext fun i => fnOf_eq_getD b i

theorem fn_bytesOf (wb : ℕ → Bool) (o : ℕ) {n i : ℕ} (hi : i < n) :
    Spec.MoussakaUnbound.fn (bytesOf wb o n) i = Keccak.witByte wb (o + i) :=
  getD_bytesOf wb o hi

/-! ## Unbound issuance -/

/-- **The spec issuance witness of a candidate**: the decoded `nf_key`, `r` (witness bytes
`[16, 32)`, `[0, 16)`), encoded by `encode_unbound_issue_witness` (with the honest committed states
of their `UCom` input). -/
def uIssueWitOf (ctxIss : Spec.Bytes) (w : ℕ → GF128) : Spec.Bytes :=
  Spec.MoussakaUnbound.encodeIssueWitness (bytesOf (bitsOf w) 16 16) ctxIss
    (bytesOf (bitsOf w) 0 16)

/-- **Unbound issuance, arithmetized → spec**: for `t` of 45 bytes, a candidate in the
arithmetized relation (`t = UCom(nf_key, ctx_iss, r)` on the 45 bytes of `t`) decodes to a witness
of the spec relation, `t = UCom(nf_key, ctx_iss, r)` as byte strings. -/
theorem uIssueRel_of_wit (t ctxIss : ByteArray) (ht : t.size = 45) (w : ℕ → GF128)
    (h : moussakaUnboundIssueWit (fun k => fnOf t k.val) (fnOf ctxIss) w) :
    Spec.MoussakaUnbound.IssueRel ⟨toL t, toL ctxIss⟩ (uIssueWitOf (toL ctxIss) w) := by
  obtain ⟨wb, hb, hrel⟩ := h
  rw [uIssueWitOf, bytesOf_bitsOf hb (by decide), bytesOf_bitsOf hb (by decide)]
  refine ⟨_, _, length_bytesOf _ _ _, length_bytesOf _ _ _, rfl, ?_⟩
  refine list_ext_getD (by rw [length_toL, ht, Spec.MoussakaUnbound.length_ucom]) fun j hj => ?_
  rw [length_toL, ht] at hj
  rw [← fnOf_eq_getD, Spec.MoussakaUnbound.ucom_getD _ _ _ ⟨j, hj⟩]
  have e := congrFun hrel ⟨j, hj⟩
  simp only at e
  rw [e]
  exact congrFun (ucom_congr (fun i hi => (fn_bytesOf wb 16 hi).symm)
    (fun i _ => fnOf_eq_getD _ _) (fun i hi => (fn_bytesOf wb 0 hi).symm)) _

/-! ## Unbound redemption -/

/-- The selected Anchor index: the first set selector bit (`64` if none). -/
def uSelOf (wb : ℕ → Bool) : ℕ := (List.range 64).findIdx fun u => wb (MoussakaUnbound.uSelBit u)

theorem uSelOf_eq {wb : ℕ → Bool} {u₀ : ℕ} (hu : u₀ < 64)
    (h : ∀ u < 64, wb (MoussakaUnbound.uSelBit u) = decide (u = u₀)) : uSelOf wb = u₀ := by
  rw [uSelOf, List.findIdx_eq (by simpa using hu)]
  simp only [List.getElem_range]
  refine ⟨by rw [h u₀ hu]; simp, fun j hj => ?_⟩
  rw [h j (by omega)]
  simp; omega

/-- **The spec redemption witness of a candidate**: the decoded `nf_key`, `r`, `s` (witness bytes
`[16, 32)`, `[0, 16)`, `[32, 151)`) and selected index, encoded by
`encode_unbound_redeem_witness`. -/
def uRedeemWitOf (ctxIss ctxRed : Spec.Bytes) (w : ℕ → GF128) : Spec.Bytes :=
  Spec.MoussakaUnbound.encodeRedeemWitness (bytesOf (bitsOf w) 16 16) ctxIss ctxRed
    (bytesOf (bitsOf w) 0 16) (bytesOf (bitsOf w) 32 119) (uSelOf (bitsOf w))

/-- **Unbound redemption, arithmetized → spec**: for at most 64 Anchors and `nf` of 24 bytes, a
candidate in the arithmetized relation decodes to a witness of the spec relation: the selected
Anchor `u`, `P_u(s) = UCom(nf_key, ctx_iss, r)` and `nf = Derive(nf_key, ctx_red)` as byte
strings (any `challenge_digest`). -/
theorem uRedeemRel_of_wit (anchors : List UovPk) (hn : anchors.length ≤ 64)
    (nf ctxIss ctxRed cd : ByteArray) (hnf : nf.size = 24) (w : ℕ → GF128)
    (h : moussakaUnboundRedeemWit GF256.ofBits (anchors.map UovPk.map) (fnOf nf) (fnOf ctxIss)
      (fnOf ctxRed) w) :
    Spec.MoussakaUnbound.RedeemRel
      ⟨anchors.map UovPk.toSpec, toL nf, toL ctxIss, toL ctxRed, toL cd⟩
      (uRedeemWitOf (toL ctxIss) (toL ctxRed) w) := by
  obtain ⟨wb, hb, u₀, hsel, ⟨hu, hpk⟩, hnfd⟩ := h
  have hu' : u₀ < anchors.length := by simpa using hu
  have hs : uSelOf (bitsOf w) = u₀ := uSelOf_eq (by omega) fun u hu64 => by
    rw [bitsOf_eq hb (by simp only [MoussakaUnbound.uSelBit, MoussakaUnbound.uRedeemOffB,
      MoussakaUnbound.uRedeemWitnessBits]; omega)]
    exact hsel u hu64
  rw [uRedeemWitOf, hs, bytesOf_bitsOf hb (by decide), bytesOf_bitsOf hb (by decide),
    bytesOf_bitsOf hb (by decide)]
  have hK : ∀ i < 16, MoussakaUnbound.uRedeemK wb i =
      Spec.MoussakaUnbound.fn (bytesOf wb 16 16) i := fun i hi => (fn_bytesOf wb 16 hi).symm
  have hR : ∀ i < 16, MoussakaUnbound.uRedeemR wb i =
      Spec.MoussakaUnbound.fn (bytesOf wb 0 16) i := fun i hi => (fn_bytesOf wb 0 hi).symm
  refine ⟨_, _, _, u₀, (anchors.map UovPk.toSpec)[u₀]'(by simpa using hu'), length_bytesOf _ _ _,
    length_bytesOf _ _ _, length_bytesOf _ _ _, List.getElem?_eq_getElem _, rfl, ?_, ?_⟩
  · refine list_ext_getD (by rw [Spec.length_eval, Spec.MoussakaUnbound.length_ucom]) fun k hk' => ?_
    rw [Spec.length_eval] at hk'
    rw [getD_eval_bytesOf _ _ _ hk', Spec.MoussakaUnbound.ucom_getD _ _ _ ⟨k, hk'⟩]
    have e := congrArg GF256.val (congrFun hpk ⟨k, hk'⟩)
    have hsd : MoussakaUnbound.uRedeemS GF256.ofBits wb =
        fun i => ⟨Keccak.witByte wb (MoussakaUnbound.uRedeemOffS + i)⟩ :=
      funext (decode_gf256 wb MoussakaUnbound.uRedeemOffS)
    simp only [hsd, MoussakaUnbound.uRedeemTarget, Moussaka.toK_gf256, List.getElem_map] at e
    simp only [List.getElem_map, UovPk.toSpec]
    exact e.trans (congrFun (ucom_congr hK (fun i _ => fnOf_eq_getD ctxIss i) hR) _)
  · refine list_ext_getD (by rw [length_toL, hnf, Spec.MoussakaUnbound.length_derive])
      fun j hj => ?_
    rw [length_toL, hnf] at hj
    rw [← fnOf_eq_getD, Spec.MoussakaUnbound.derive_getD _ _ ⟨j, hj⟩, hnfd ⟨j, hj⟩]
    exact congrFun (derive_congr hK (fun i _ => fnOf_eq_getD ctxRed i)) _

/-! ## `hinj` for the C++ instance encodings -/

/-- **`hinj` for unbound issuance families** whose instance encoding is the C++ one, `t ‖ ctx_iss`
(`UnboundIssueRelation::hash_instance`), with `t` of fixed length and the family injective. -/
theorem hinj_unboundIssue {ι : Type} (stF : ι → Statement) (inst : ι → ByteArray × ByteArray)
    (henc : ∀ s, (stF s).instEnc ByteArray.empty =
      toBA (Spec.MoussakaUnbound.IssueInstance.encode ⟨toL (inst s).1, toL (inst s).2⟩))
    (n : ℕ) (hlen : ∀ s, (inst s).1.size = n) (hi : Function.Injective inst) :
    Function.Injective fun s => (stF s).instEnc ByteArray.empty := by
  intro s s' h
  simp only [henc, Spec.MoussakaUnbound.IssueInstance.encode] at h
  obtain ⟨h1, h2⟩ := List.append_inj (toBA_inj h) (by simp [length_toL, hlen])
  exact hi (Prod.ext (toL_inj h1) (toL_inj h2))

/-- **`hinj` for unbound redemption families** whose instance encoding is the C++ one
(`hash_redeem_instance`, shared with bound redemption): as `hinj_moussakaRedeem`, Anchor keys with
32-byte digests, fewer than 256 Anchors, `nf` and the contexts of fixed lengths, and the family
injective on `(digests of the Anchors, nf, ctx_iss, ctx_red, challenge_digest)`. -/
theorem hinj_unboundRedeem {ι : Type} (stF : ι → Statement) (anc : ι → List UovPk)
    (nf ctxIss ctxRed cd : ι → ByteArray)
    (henc : ∀ s, (stF s).instEnc ByteArray.empty = toBA (Spec.Moussaka.RedeemInstance.encode
      ⟨(anc s).map UovPk.toSpec, toL (nf s), toL (ctxIss s), toL (ctxRed s), toL (cd s)⟩))
    (hdig : ∀ s, ∀ pk ∈ anc s, pk.digest.size = 32) (hn : ∀ s, (anc s).length < 256)
    (nN nI nR : ℕ) (hnf : ∀ s, (nf s).size = nN) (hci : ∀ s, (ctxIss s).size = nI)
    (hcr : ∀ s, (ctxRed s).size = nR)
    (hi : Function.Injective fun s =>
      ((anc s).map UovPk.digest, nf s, ctxIss s, ctxRed s, cd s)) :
    Function.Injective fun s => (stF s).instEnc ByteArray.empty := by
  intro s s' h
  have h' : (moussakaRedeem (anc s) (nf s) (ctxIss s) (ctxRed s) (cd s) false).instEnc
      ByteArray.empty =
      (moussakaRedeem (anc s') (nf s') (ctxIss s') (ctxRed s') (cd s') false).instEnc
        ByteArray.empty := by
    simp only [henc] at h
    simpa only [moussakaRedeem] using h
  exact hinj_moussakaRedeem anc nf ctxIss ctxRed cd false hdig hn nN nI nR hnf hci hcr hi h'

theorem hinj_refIssue {ι : Type} (lr : Bool) (inst : ι → ByteArray × ByteArray) (n : ℕ)
    (hlen : ∀ s, (inst s).1.size = n) (hi : Function.Injective inst) :
    Function.Injective fun s =>
      (Unbound.refIssue lr (inst s).1 (inst s).2).instEnc ByteArray.empty :=
  hinj_unboundIssue _ inst (fun _ => rfl) n hlen hi

theorem hinj_refRedeem {ι : Type} (lr : Bool) (anc : ι → List UovPk)
    (nf ctxIss ctxRed cd : ι → ByteArray)
    (hdig : ∀ s, ∀ pk ∈ anc s, pk.digest.size = 32) (hn : ∀ s, (anc s).length < 256)
    (nN nI nR : ℕ) (hnf : ∀ s, (nf s).size = nN) (hci : ∀ s, (ctxIss s).size = nI)
    (hcr : ∀ s, (ctxRed s).size = nR)
    (hi : Function.Injective fun s =>
      ((anc s).map UovPk.digest, nf s, ctxIss s, ctxRed s, cd s)) :
    Function.Injective fun s =>
      (Unbound.refRedeem lr (anc s) (nf s) (ctxIss s) (ctxRed s) (cd s)).instEnc
        ByteArray.empty :=
  hinj_unboundRedeem _ anc nf ctxIss ctxRed cd (fun _ => rfl) hdig hn nN nI nR hnf hci hcr hi

end VoleMole.EndToEnd.SpecRel
