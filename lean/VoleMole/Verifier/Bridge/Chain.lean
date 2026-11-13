import VoleMole.Verifier.Bridge.Columns
import VoleMole.Verifier.Bridge.Relations

/-!
# Bridge: the executable verifier on a whole chain of challenges

`Bridge/Relations.lean` proves that acceptance gives `EndToEnd`'s accepting equation at the one
`Δ` of the accepted transcript. The `*_extract_gf128` theorems need more: on the chain's whole
accepting set `A` of challenges, `Claim4Hyp` (per-tree and KOS-affine witness rows, injective
lift) and the accepting equation with one fixed remainder `R`. This file derives both for the
executable verifier, leaving the probabilistic hypotheses explicit.

## The chain (`Chain`, `Chain.OnChain`)

Transcript order: the prover commits (corrections `c_i`, `c_mult`, `iv_pre`, the leaf commitments),
receives `chal1 = H₂¹(…)`, sends `ũ` and `d`, the verifier's VOLE hash `h_V` goes into
`chal2 = H₂²(y)`, the prover sends `ã` and the check value `z`, and `chal3 = H₂³(chal2 ‖ z ‖ ã ‖ ctr)`
must equal `Δ`. A *chain* (L4 §1) fixes everything up to the `H₂³` input: here a reference proof
(`Chain.proof`: its `c_i`, `c_mult`, `ũ`, `d`, `ã`, `iv_pre`, `ctr`; its `Δ` and opening are not used),
the committed leaf keys `K i j` (L1), `iv` and the gate-hash function `h5`, `chal1`, `h_V` and
`z`, and `chal2` with the constraint evaluator `vals` of the QuickSilver check. For the verifier
with hash functions `Hs` (`Verifier/Hashes.lean`), `iv = H₄(iv_pre ‖ mu₁ ‖ 4)`, `h5 = H₅`,
`chal2 = H₂²(…)` and `vals = st.values chal1 (H_comb(chal2 ‖ dst))` (the combination bytes, for the
combined relations), all determined before any `Δ`; they are fields, with those equations
hypotheses of `onChain_of_accept`, so that `Prob/` can sample `chal2` and `l` independently and
`ROM/` can read them from an oracle table. `Δ` determines only the opening, the verifier's
responses and whether `chal3` hits it.

The verifier's responses at a challenge `Δ'` are the committed response `Chain.resp`
(`respAt`: ConvertToVOLE and the CRT step from the commitments, `Bridge/Columns.lean`), a function
of `Δ'` fixed before `chal1`. `Δ' ∈ A` means `Chain.OnChain`: at `Δ'` the committed responses
reproduce the chain's `h_V` (its `H₂²` input) and `z` (its `H₂³` input), and `Δ_lifted ≠ 0`.
`onChain_of_accept`: a proof of the chain that the executable verifier accepts, whose opening
reconstructs the committed keys (L1), is on the chain at its own `Δ`, and its `Δ` is the chain's
`chal3`. This is how `hclaim1` (accepted ⇒ in `A`) is met.

## What is derived (`chain_claim4`)

From `OnChain` on `A`, the KOS good event `KOSGood` on `S ⊇ A` (L3, the probability over `chal1`)
and `IsFixed` for the trees with a dead leaf (L2):
* `Claim4Hyp (lift T) A known u Q u*`: `lift_inj` is `lift_injective` (kernel-checked left inverse
  of `W_CRT`); `tree_form` is `resp_row` (ConvertToVOLE affine in each `Δ_i`, `W_CRT` linear),
  with `u^{(i)} = c_i + Σ_j PRG(K i j)` the extractor's corrected small-VOLE value; `consistent`
  comes from `KOSGood` applied to the VOLE check, which on a chain passes with the chain's `h_V`
  (`kos_onChain`, via `map_voleHashReceiver`); `unknown_fixed` is L2;
* the accepting equation on all of `A` with `R = maskPoly d a b ã z`, where `a_i + b_i·Δ` is the
  affine form of the mask rows that the same `KOSGood` gives, so `R` does not depend on `Δ`.

## Per relation (`*_extract_chain`)

The `*_extract_gf128` theorems applied to the executable verifier's chains. What remains assumed:
* `hkos`: `chal1` is good for the committed responses (L3, `Seed.card_not_kosGood_le`);
* `hL2`: trees with a dead leaf have a fixed block on `A` (L2);
* `hQS`, `hcomb`: `chall₂` (and `l`) are good for `w* = u* + d`, the slope of the witness rows on
  `A` (unique when `|A| ≥ 2`, and then the canonical slope of L4 §5, fixed before `chal2`);
* `hδ`, `hclaim1`: admissible `chal3` decode injectively, and accepted ones lie in `A` (L1, with
  `onChain_of_accept`);
* `A ⊆ {OnChain}`: the definition of the chain's accepting set (its `H₂²` and `H₂³` inputs are the
  verifier's), and the binding of the leaf commitments (`hbind` in `onChain_of_accept`).

`Prob/ChainRelations.lean` (`*_chain_prob`) discharges `hkos`, `hQS`, `hcomb` and `hδ` for uniform
independent `chal1`, `chal2` and `l` (L3, L4 with the canonical slope `Chain.uCanon`).
-/

open Finset Polynomial

namespace VoleMole.Verifier.Bridge

-- The statements hold for any CTR PRG (`HasPrg`, `Verifier/Prg.lean`), AES included.
variable [VoleMole.Verifier.HasPrg]
set_option linter.unusedSectionVars false

open VoleMole.Arith VoleMole.Verifier VoleMole.EndToEnd VoleMole.SeedExtraction

noncomputable section

@[simp] lemma gfId_apply (x : GF128) : gfId x = x := rfl

/-! ## The chain -/

/-- The prover's side of one chain: everything fixed before `Δ`. -/
structure Chain where
  /-- A proof of the chain; its `c_i`, `c_mult`, `ũ`, `d`, `ã`, `iv_pre` and `ctr` are the chain's
  (its `Δ` and opening are not used). -/
  proof : ByteArray
  /-- The committed leaf keys `K i j` (leaf `j` of vector `i`; L1). -/
  keys : ℕ → ℕ → ByteArray
  /-- `iv`. For the verifier with hashes `Hs` it is `H₄(iv_pre ‖ mu₁ ‖ 4)` (`ivOf`, a hypothesis
  of `onChain_of_accept`). -/
  iv : ByteArray
  /-- The gate hash `H₅` the committed responses use (`Hs.hash .h5`, a hypothesis of
  `onChain_of_accept`). -/
  h5 : ByteArray → ByteArray
  /-- `chal1`. -/
  chal1 : ByteArray
  /-- The verifier's VOLE hash `h_V` in the `H₂²` input. -/
  hV : Array GF128
  /-- The QuickSilver check value `z` in the `H₂³` input. -/
  z : GF128
  /-- `chal2`. For the verifier it is `H₂²(chal1 ‖ ũ ‖ h_V ‖ [mu] ‖ binder₂ ‖ d ‖ 10)`
  (`Verifier.chal2`, a hypothesis of `onChain_of_accept`); as a field it can be sampled
  (`Prob/`). -/
  chal2 : ByteArray
  /-- The constraint evaluator of the QuickSilver check. For the verifier it is
  `st.values chal1 (st.combBytes Hs chal2)` (a hypothesis of `onChain_of_accept`), which for the
  combined relations reads `l = H_comb(chal2 ‖ dst)`; as a field, `l` can be sampled independently
  (`Prob/`). -/
  vals : (ℕ → GF128) → List GF128

namespace Chain

variable (st : Statement) (ch : Chain) (T : CrtTables)

/-- The reference proof. -/
def pf : Proof := { params := st.params, bytes := ch.proof }

/-- The corrections `c_i`. -/
def corr (i : ℕ) : ByteArray :=
  (ch.pf st).corrections.extract ((i - 1) * st.params.correctionBytes)
    (i * st.params.correctionBytes)

/-- **The committed response at `Δ'`**: the verifier's CRT output computed from the commitments. -/
def resp (Δ : Blocks) : CrtOut :=
  respAt ch.h5 T st.params (ch.pf st).corrections (ch.pf st).cmult ch.iv ch.keys Δ

/-- The verifier's QuickSilver check value at `Δ'`, from the committed responses. -/
def check (Δ : Blocks) : GF128 :=
  let crt := ch.resp st T Δ
  let deltaL := crt.deltaLifted.toGF
  qsCheck (ch.pf st) ch.chal2
    (constraintKeys st.params (correctedKeys (ch.pf st) crt.rows deltaL) deltaL (ch.vals))
    crt.qMask deltaL

/-- **`Δ'` is on the chain**: the committed responses at `Δ'` give `Δ_lifted ≠ 0`, the chain's
`h_V` (the verifier's `H₂²` input is the chain's) and the chain's `z` (its `H₂³` input is too). -/
def OnChain (Δ : Blocks) : Prop :=
  (ch.resp st T Δ).deltaLifted.toGF ≠ 0 ∧
    voleHashReceiver st.params ch.chal1 (ch.resp st T Δ).rows (ch.resp st T Δ).qMask
      (ch.resp st T Δ).deltaLifted.toGF (ch.pf st).voleCheck = ch.hV ∧
    ch.check st T Δ = ch.z

/-- The witness rows of the committed response (`Claim4Hyp`'s `Q`). -/
def Qw (j : Fin st.params.witnessBits) (Δ : Blocks) : GF128 := (ch.resp st T Δ).rows[(j : ℕ)]!.toGF

/-- The correction `d` (`EndToEnd`'s `dc`). -/
def dc (j : Fin st.params.witnessBits) : Bool := corrBit (ch.pf st) j

/-- The extractor's corrected small-VOLE values `u^{(i)}` (`Claim4Hyp`'s `u`). -/
def u (i : Fin BAVC.tau) (j : Fin st.params.witnessBits) : Bool :=
  uBit st.params ch.iv (ch.corr st) ch.keys i j

/-- The number `L = ℓ' + d − 1` of rows the VOLE check hashes. -/
def kosL : ℕ := st.params.correctionRows + (st.params.qsDegree - 1)

/-- The hashed rows of the committed response (`KOSGood`'s `Q`). -/
def kosQ (Δ : Blocks) (k : Fin (kosL st)) : GF128 :=
  (hashedRows st.params (ch.resp st T Δ).rows (ch.resp st T Δ).qMask)[(k : ℕ)]!

/-- The four direct masks of the committed response (`KOSGood`'s `D`). -/
def kosD (Δ : Blocks) (j : Fin 4) : GF128 :=
  (ch.resp st T Δ).qMask[st.params.qsDegree - 1 + j]!.toGF

/-- The prover's `ũ`. -/
def kosU (j : Fin 4) : GF128 := gfOfBytes (ch.pf st).voleCheck (16 * j)

end Chain

/-- The `2⁶⁴` short keys `t` of VOLEHash and ZKHash (field elements of degree `< 64`). -/
def shortKeys : Finset GF128 := (range (2 ^ 64)).image fun n => ⟨n.toUInt64, 0⟩

lemma mem_shortKeys (w : UInt64) : gfId ⟨w, 0⟩ ∈ shortKeys :=
  Finset.mem_image.2 ⟨w.toNat, Finset.mem_range.2 w.toNat_lt, by simp [gfId]⟩

/-- `chal1` as a VOLEHash challenge. -/
def Chain.kosCh (ch : Chain) : Seed.Ch GF128 shortKeys := chOf gfId mem_shortKeys ch.chal1

/-! ## Sizes and entries of the committed response -/

namespace Chain

variable (st : Statement) (ch : Chain) (T : CrtTables)

lemma resp_rows_size (Δ : Blocks) : (ch.resp st T Δ).rows.size = st.params.correctionRows := by
  simp [resp, respAt, crtReconstructAt, crtReconstructWith]

lemma resp_qMask_size (Δ : Blocks) : (ch.resp st T Δ).qMask.size = st.params.nMask := by
  simp [resp, respAt, crtReconstructAt, crtReconstructWith]

lemma resp_deltaL (Δ : Blocks) : (ch.resp st T Δ).deltaLifted.toGF = lift T Δ := by
  simp only [resp, respAt, crtReconstructAt, crtReconstructWith]
  rw [rowMul_lift, blocksOf_dbitOf]

lemma hashedRows_size (Δ : Blocks) :
    (hashedRows st.params (ch.resp st T Δ).rows (ch.resp st T Δ).qMask).size = kosL st := by
  simp only [hashedRows, Array.size_append, Array.size_map, Array.size_extract, resp_rows_size,
    resp_qMask_size, kosL, Params.nMask]
  omega

lemma kosQ_row (Δ : Blocks) {j : ℕ} (hj : j < st.params.correctionRows) :
    ch.kosQ st T Δ ⟨j, by unfold kosL; omega⟩ = (ch.resp st T Δ).rows[j]!.toGF := by
  have hs := ch.resp_rows_size st T Δ
  simp only [kosQ, hashedRows]
  rw [getElem!_pos _ _ (by simp [hs]; omega), Array.getElem_append_left (by simp [hs, hj])]
  simp [getElem!_pos, hs, hj]

lemma kosQ_mask (Δ : Blocks) {i : ℕ} (hi : i < st.params.qsDegree - 1) :
    ch.kosQ st T Δ ⟨st.params.correctionRows + i, by unfold kosL; omega⟩ =
      (ch.resp st T Δ).qMask[i]!.toGF := by
  have hs := ch.resp_rows_size st T Δ
  have hm := ch.resp_qMask_size st T Δ
  have hi' : i < st.params.nMask := by unfold Params.nMask; omega
  simp only [kosQ, hashedRows]
  rw [getElem!_pos _ _ (by simp [hs, hm]; omega), Array.getElem_append_right (by simp [hs])]
  simp [getElem!_pos, hs, hm, hi']

end Chain

/-! ## The VOLE check on a chain -/

lemma voleHash_getElem! {T : Finset GF128} (c : Seed.Ch GF128 T) (xs : Array GF128) {L : ℕ}
    (h : xs.size = L) :
    Seed.voleHash c (fun k : Fin xs.size => xs[k]) = Seed.voleHash c (fun k : Fin L => xs[(k : ℕ)]!) := by
  subst h
  congr 1
  funext k
  simp [getElem!_pos]

/-- **The VOLE check of the committed response is `Seed.kosValue`**, at every `Δ'`. -/
theorem vole_kosValue (st : Statement) (ch : Chain) (T : CrtTables) (Δ : Blocks) (i : Fin 4) :
    (voleHashReceiver st.params ch.chal1 (ch.resp st T Δ).rows (ch.resp st T Δ).qMask
      (ch.resp st T Δ).deltaLifted.toGF (ch.pf st).voleCheck)[(i : ℕ)]! =
      Seed.kosValue ch.kosCh (lift T) (ch.kosQ st T) (ch.kosD st T) (ch.kosU st) Δ i := by
  have h := map_voleHashReceiver gfId mem_shortKeys st.params ch.chal1 (ch.resp st T Δ).rows
    (ch.resp st T Δ).qMask (ch.resp st T Δ).deltaLifted.toGF (ch.pf st).voleCheck i
  simp only [gfId_apply] at h
  rw [h]
  simp only [Seed.kosValue, Chain.kosCh, Chain.resp_deltaL]
  rw [voleHash_getElem! _ _ (ch.hashedRows_size st T Δ)]
  rfl

/-- On a chain the VOLE check passes with the chain's `h_V`. -/
theorem kos_onChain (st : Statement) (ch : Chain) (T : CrtTables) {Δ : Blocks}
    (h : ch.OnChain st T Δ) :
    Seed.kosValue ch.kosCh (lift T) (ch.kosQ st T) (ch.kosD st T) (ch.kosU st) Δ =
      fun j : Fin 4 => ch.hV[(j : ℕ)]! := by
  funext j
  rw [← vole_kosValue, h.2.1]

/-! ## The accepting equation at one `Δ'`, with affine masks -/

/-- `accept_hacc`'s computation at `gfId`, for any mask MACs `a_i + b_i·Δ` and without
acceptance: the verifier's check value `z` gives `qsCheck + maskPoly d a b ã z = 0`, for any
constraint evaluator `vals` that is `System.values` of a system `cs` of degree `≤ d`. -/
theorem hacc_at (st : Statement) (vals : (ℕ → GF128) → List GF128) (cs : System GF128)
    (hvals : ∀ x, vals x = cs.values x) (hdeg : ∀ e ∈ cs, e.degree ≤ st.params.qsDegree)
    (bytes c2 : ByteArray) (rows qMask : Array W128) {deltaL : GF128} (hΔ : deltaL ≠ 0)
    (a b : ℕ → GF128)
    (hmask : ∀ i < st.params.qsDegree - 1, qMask[i]!.toGF = a i + b i * deltaL) :
    let pf : Proof := { params := st.params, bytes := bytes }
    EndToEnd.qsCheck cs st.params.qsDegree
        (Seed.zkCoeff cs.length (gfOfBytes c2 0) (gfOfBytes c2 16) (gfOfBytes c2 32)
          ⟨W128.word c2 48, 0⟩)
        (extW fun j : Fin st.params.witnessBits =>
          rows[(j : ℕ)]!.toGF + SeedExtraction.bit (corrBit pf j) * deltaL) deltaL +
      (Seed.maskPoly st.params.qsDegree a b (fun i => gfOfBytes pf.qsProof (16 * (i - 1)))
        (qsCheck pf c2 (constraintKeys st.params (correctedKeys pf rows deltaL) deltaL vals)
          qMask deltaL)).eval deltaL = 0 := by
  intro pf
  have hm := map_correctedKeys gfId pf rows deltaL
  have h := hacc_of_qsCheck gfId pf c2 (constraintKeys st.params (correctedKeys pf rows deltaL)
    deltaL vals) qMask deltaL cs
    (fun j => gfId ((correctedKeys pf rows deltaL).getD j 0)) ?_ a b hmask
  · rw [hm] at h
    exact h
  · rw [map_constraintKeys gfId GF128.card_eq _ _ _ _ _
      (fun x => (List.map_id _).trans (hvals x))]
    congr 1
    funext k
    rw [keyVals, sysQS]
    exact (mac_constraintQS _ (show gfId.toFun deltaL ≠ 0 from hΔ) _
      (hdeg _ (List.get_mem _ k))).symm

/-! ## `Claim4Hyp` and the accepting equation on the chain -/

lemma witnessBits_le (p : Params) : p.witnessBits ≤ p.correctionRows := by
  unfold Params.correctionRows; split <;> omega

/-- **`tree_form` for the committed witness rows** (`resp_row`): every tree contributes
`u^{(i)}[j] · e_i(Δ'_i)`, and the trees outside `known` have a fixed block on `A` (L2). -/
theorem chain_tree_form (T : CrtTables) (st : Statement) (ch : Chain) (A : Finset Blocks)
    {known : Finset (Fin BAVC.tau)} (hL2 : ∀ i ∉ known, IsFixed (A : Set Blocks) i)
    (j : Fin st.params.witnessBits) :
    ∃ c, ∀ Δ ∈ (A : Set Blocks), ch.Qw st T j Δ =
      c + ∑ i ∈ known, SeedExtraction.bit (ch.u st i j) * blockLift (lift T) i (Δ i) := by
  classical
  have hform : ∀ Δ, ch.Qw st T j Δ = rowConst T st.params ch.iv ch.keys j +
      ∑ i, SeedExtraction.bit (ch.u st i j) * blockLift (lift T) i (Δ i) := by
    intro Δ
    have := resp_row ch.h5 T st.params (dbitOf Δ) (ch.corr st) (ch.pf st).cmult ch.iv ch.keys
      (r := j) (lt_of_lt_of_le j.isLt (witnessBits_le _))
    rw [blocksOf_dbitOf] at this
    exact this
  rcases A.eq_empty_or_nonempty with hA0 | ⟨Δ₀, hΔ₀⟩
  · exact ⟨0, fun Δ hΔ => by simp [hA0] at hΔ⟩
  refine ⟨rowConst T st.params ch.iv ch.keys j + ∑ i ∈ univ.filter (· ∉ known),
    SeedExtraction.bit (ch.u st i j) * blockLift (lift T) i (Δ₀ i), fun Δ hΔ => ?_⟩
  have hk : univ.filter (· ∈ known) = known := by ext; simp
  have hfix : ∑ i ∈ univ.filter (· ∉ known),
      SeedExtraction.bit (ch.u st i j) * blockLift (lift T) i (Δ i) =
      ∑ i ∈ univ.filter (· ∉ known),
        SeedExtraction.bit (ch.u st i j) * blockLift (lift T) i (Δ₀ i) :=
    Finset.sum_congr rfl fun i hi => by rw [hL2 i (Finset.mem_filter.1 hi).2 Δ hΔ Δ₀ hΔ₀]
  rw [hform, ← Finset.sum_filter_add_sum_filter_not univ (· ∈ known), hk, hfix]
  ring

/-- **L3 on the chain**: on a KOS-good `chal1` the hashed rows of the committed responses are
affine on `A`: witness rows `v_j + e(Δ')·u_j`, masks `a_i + b_i·e(Δ')`. -/
theorem chain_kos_affine (T : CrtTables) (st : Statement) (ch : Chain) {A : Finset Blocks}
    (hA : ∀ Δ ∈ A, ch.OnChain st T Δ) {S : Set Blocks} (hAS : (A : Set Blocks) ⊆ S)
    (hkos : Seed.KOSGood ch.kosCh S (lift T) (ch.kosQ st T) (ch.kosD st T)) :
    ∃ uQ vQ : ℕ → GF128,
      (∀ j < st.params.correctionRows, ∀ Δ ∈ A,
        (ch.resp st T Δ).rows[j]!.toGF = vQ j + lift T Δ * uQ j) ∧
      (∀ i < st.params.qsDegree - 1, ∀ Δ ∈ A,
        (ch.resp st T Δ).qMask[i]!.toGF =
          vQ (st.params.correctionRows + i) + uQ (st.params.correctionRows + i) * lift T Δ) := by
  obtain ⟨uQ, vQ, _, _, hline⟩ := hkos (ch.kosU st) (fun j : Fin 4 => ch.hV[(j : ℕ)]!) A hAS
    fun Δ hΔ => kos_onChain st ch T (hA Δ (Finset.mem_coe.1 hΔ))
  let ext : (Fin (Chain.kosL st) → GF128) → ℕ → GF128 := fun f k =>
    if hk : k < Chain.kosL st then f ⟨k, hk⟩ else 0
  refine ⟨ext uQ, ext vQ, fun j hj Δ hΔ => ?_, fun i hi Δ hΔ => ?_⟩
  · have hk : j < Chain.kosL st := by unfold Chain.kosL; omega
    have := congrFun (hline Δ (Finset.mem_coe.2 hΔ)).1 ⟨j, hk⟩
    rw [ch.kosQ_row st T Δ hj] at this
    simpa [ext, hk] using this
  · have hk : st.params.correctionRows + i < Chain.kosL st := by unfold Chain.kosL; omega
    have := congrFun (hline Δ (Finset.mem_coe.2 hΔ)).1 ⟨_, hk⟩
    rw [ch.kosQ_mask st T Δ hi] at this
    simpa [ext, hk, mul_comm] using this

/-- **The hypotheses of `*_extract_gf128` for the executable verifier's chain.** If every
`Δ' ∈ A` is on the chain, `chal1` is KOS-good for the committed responses on `S ⊇ A` (L3), and
the trees outside `known` have a fixed block on `A` (L2), then for some slope `u*` (the slope of
the witness rows on `A`) `Claim4Hyp` holds with the executable lift, the committed witness rows
and the extractor's `u^{(i)}`, and there is one remainder `R` of degree `≤ d − 1` with the
accepting equation on all of `A`. -/
theorem chain_claim4 {T : CrtTables} (hT : liftInvOk T = true) (st : Statement) (ch : Chain)
    (cs : System GF128) (hvals : ∀ x, ch.vals x = cs.values x)
    (hdeg : ∀ e ∈ cs, e.degree ≤ st.params.qsDegree)
    {A : Finset Blocks} (hA : ∀ Δ ∈ A, ch.OnChain st T Δ) {S : Set Blocks}
    (hAS : (A : Set Blocks) ⊆ S)
    (hkos : Seed.KOSGood ch.kosCh S (lift T) (ch.kosQ st T) (ch.kosD st T))
    {known : Finset (Fin BAVC.tau)} (hL2 : ∀ i ∉ known, IsFixed (A : Set Blocks) i) :
    ∃ (uStar : Fin st.params.witnessBits → GF128) (R : GF128[X]),
      R.natDegree ≤ st.params.qsDegree - 1 ∧
      Claim4Hyp (lift T) (A : Set Blocks) known (ch.u st) (ch.Qw st T) uStar ∧
      ∀ Δ ∈ A, EndToEnd.qsCheck cs st.params.qsDegree
          (Seed.zkCoeff cs.length (gfOfBytes ch.chal2 0)
            (gfOfBytes ch.chal2 16) (gfOfBytes ch.chal2 32)
            ⟨W128.word ch.chal2 48, 0⟩)
          (macs (lift T) (ch.Qw st T) (ch.dc st) Δ) (lift T Δ) + R.eval (lift T Δ) = 0 := by
  obtain ⟨uQ, vQ, hrow, hmask⟩ := chain_kos_affine T st ch hA hAS hkos
  let a : ℕ → GF128 := fun i => vQ (st.params.correctionRows + i)
  let b : ℕ → GF128 := fun i => uQ (st.params.correctionRows + i)
  refine ⟨fun j => uQ j,
    Seed.maskPoly st.params.qsDegree a b (fun i => gfOfBytes (ch.pf st).qsProof (16 * (i - 1)))
      ch.z, Seed.maskPoly_natDegree_le _ _ _ _ _,
    ⟨lift_injective hT, chain_tree_form T st ch A hL2, fun j => ⟨vQ j, fun Δ hΔ => ?_⟩, hL2⟩,
    fun Δ hΔ => ?_⟩
  · rw [Chain.Qw, hrow j (lt_of_lt_of_le j.isLt (witnessBits_le _)) Δ (Finset.mem_coe.1 hΔ),
      mul_comm]
  · have hon := hA Δ hΔ
    have h := hacc_at st ch.vals cs hvals hdeg ch.proof ch.chal2 (ch.resp st T Δ).rows
      (ch.resp st T Δ).qMask hon.1 a b fun i hi => by
        rw [hmask i hi Δ hΔ, ch.resp_deltaL st T Δ]
    have hz : ch.check st T Δ = ch.z := hon.2.2
    simp only [Chain.check, Chain.pf] at hz
    dsimp only at h
    rw [hz, ch.resp_deltaL st T Δ] at h
    exact h

/-! ## Accepted proofs of the chain are on the chain -/

/-- The fields of a proof that a chain fixes: `c_i`, `c_mult`, `iv_pre` (the `H₂¹` input), `ũ`, `d`
(the `H₂²` input), `ã` and `ctr` (the `H₂³` input). -/
def ChainFields (st : Statement) (ch : Chain) (proof : ByteArray) : Prop :=
  let pf : Proof := { params := st.params, bytes := proof }
  pf.corrections = (ch.pf st).corrections ∧ pf.cmult = (ch.pf st).cmult ∧
    pf.ivPre = (ch.pf st).ivPre ∧ pf.voleCheck = (ch.pf st).voleCheck ∧
    pf.correction = (ch.pf st).correction ∧ pf.qsProof = (ch.pf st).qsProof ∧
    pf.ctr = (ch.pf st).ctr

/-- **An accepted proof of the chain lies on the chain, at its own `Δ`, and its `Δ` is the
chain's `chal3`.** For the verifier with hash functions `Hs`. Hypotheses: the proof has the
chain's fields; its opening reconstructs the committed keys off the hidden leaves and the
verifier's `chal1` is the chain's (L1: the leaf commitments bind); and the verifier's `h_V` and
check value are the chain's (the proof's `H₂²` and `H₂³` inputs are the chain's). The verifier's
run is then the committed response (`crtReconstruct_eq_respAt`), so `OnChain` holds at
`Δ' = blocksOf (deltaBit Δ)`: this is `hclaim1` (accepted `chal3` lie in `A`). The chain's `iv`,
gate hash, `chal2` and constraint evaluator must be the verifier's (`hiv`, `hh5`, `hc2`, `hvals`;
for a chain built from a run of the verifier all are `rfl`). -/
theorem onChain_of_accept (Hs : Hashes) (T : CrtTables) (st : Statement) (ch : Chain)
    (hiv : ch.iv = ivOf Hs (ch.pf st) (st.mu1 Hs)) (hh5 : ch.h5 = Hs.hash .h5)
    (hc2 : ch.chal2 = Verifier.chal2 Hs (ch.pf st) ch.chal1 ch.hV (st.muDelayed Hs ch.chal1)
      st.binder2)
    (hvals : ch.vals = st.values ch.chal1 (st.combBytes Hs ch.chal2)) (proof : ByteArray)
    (h : (verify Hs T st proof).accept = true) (hf : ChainFields st ch proof)
    (hrun : let pf : Proof := { params := st.params, bytes := proof }
      ∀ leaves, BAVC.reconstruct ch.iv pf.opening pf.delta = some leaves →
        (∀ i < BAVC.tau, ∀ j < 2 ^ BAVC.kOf i, j ≠ BAVC.deltaIndex pf.delta i →
          leafKey leaves i j = ch.keys i j) ∧
        chal1 Hs pf (st.mu1 Hs) (BAVC.check (Hs.hash .h1) leaves.coms) st.binder1 = ch.chal1 ∧
        let crt := crtReconstruct Hs pf T ch.iv (convertToVole pf ch.iv leaves)
        let deltaL := crt.deltaLifted.toGF
        voleHashReceiver st.params ch.chal1 crt.rows crt.qMask deltaL pf.voleCheck = ch.hV ∧
        qsCheck pf (chal2 Hs pf ch.chal1 ch.hV (st.muDelayed Hs ch.chal1) st.binder2)
          (constraintKeys st.params (correctedKeys pf crt.rows deltaL) deltaL
            (st.values ch.chal1 (st.combBytes Hs
              (chal2 Hs pf ch.chal1 ch.hV (st.muDelayed Hs ch.chal1) st.binder2))))
          crt.qMask deltaL = ch.z) :
    let pf : Proof := { params := st.params, bytes := proof }
    ch.OnChain st T (blocksOf (BAVC.deltaBit pf.delta)) ∧
      chal3 Hs (ch.pf st) ch.chal2 ch.z = pf.delta := by
  obtain ⟨-, leaves, hr, h0, h3⟩ := (accept_iff Hs T st proof).1 h
  obtain ⟨hc, hm, hiv0, hu, hd, hq, hctr⟩ := hf
  dsimp only at hrun
  set pf : Proof := { params := st.params, bytes := proof } with hpf
  have hiv' : ivOf Hs pf (st.mu1 Hs) = ch.iv := by
    simp only [ivOf, hiv]; rw [hiv0]
  rw [hiv'] at hr h0 h3
  obtain ⟨hbind, hc1, hV, hz⟩ := hrun leaves hr
  have hresp : crtReconstruct Hs pf T ch.iv (convertToVole pf ch.iv leaves) =
      ch.resp st T (blocksOf (BAVC.deltaBit pf.delta)) := by
    rw [crtReconstruct_eq_respAt Hs T pf _ leaves ch.keys hbind, Chain.resp, hc, hm, hh5]
  have hc2' : chal2 Hs pf ch.chal1 ch.hV (st.muDelayed Hs ch.chal1) st.binder2 = ch.chal2 := by
    simp only [hc2, Verifier.chal2, chal2Input, hu, hd]
  have hck : ∀ (c2 : ByteArray) (rows qMask : Array W128) (dl : GF128),
      qsCheck pf c2 (constraintKeys st.params (correctedKeys pf rows dl) dl
        (st.values ch.chal1 (st.combBytes Hs c2))) qMask dl =
      qsCheck (ch.pf st) c2 (constraintKeys st.params (correctedKeys (ch.pf st) rows dl) dl
        (st.values ch.chal1 (st.combBytes Hs c2))) qMask dl := by
    intro c2 rows qMask dl
    simp only [qsCheck, correctedKeys, hq, hd]
    rfl
  rw [hresp] at hV hz h0 h3
  rw [hc2', hck] at hz
  rw [hc1, hV, hc2', hck] at h3
  rw [hu] at hV
  dsimp only
  refine ⟨?_, ?_⟩
  · refine ⟨h0, hV, ?_⟩
    simp only [Chain.check, hvals]
    exact hz
  rw [← h3]
  simp only [chal3, chal3Input] at hz ⊢
  rw [hz, hq, hctr]

end

end VoleMole.Verifier.Bridge
