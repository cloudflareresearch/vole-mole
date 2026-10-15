import VoleMole.ZK.IdealFields
import VoleMole.ZK.CMult
import VoleMole.ZK.QsIdeal
import VoleMole.ZK.CrtMaskTables
import VoleMole.ZK.Masking
import VoleMole.ZK.Grinding

/-!
# With the ideal tape, the prover's proofs are distributed as the simulator's (`lean/docs/zk.md` H5–H7)

The ideal-tape prover `Sim.proveIdeal` (the executable prover's computation with the random
sources of hybrids H1–H4 and H6 replaced by the tape) and the simulator `Sim.simulate` (uniform
fields) have the same output distribution, for every hash record `Hs` and every witness that
satisfies the statement's system. The hops, composed:

* H5, corrections and `d` (`Masking.corrections_equiv`): each byte of `c_i = u^{(0)} ⊕ u^{(i)}`
  and of `d = u^{(0)} ⊕ w` is a one-time pad (`upush_rows`);
* H6, `c_mult` (`Masking.cmultEquiv`): the tape's sibling `H₅` answers pad it bit by bit
  (`Sim.upush_cmult`, `N_MASK ≤ 32`);
* §7.4, the CRT masks: uniform pads give uniform `u_mask` (`ZK.balanced_crtVal`, a kernel-checked
  certificate for faest-arch-opt's tables);
* H7, the responses (`Masking.kosQsEquiv`): `ũ` is the four direct masks plus a function of the
  others, and `ã` the QuickSilver response (`qsResponse`) of the `d − 1` other masks, whose
  coefficients depend on the masks only through `ũ` (`chal2` hashes `h_V`, which is the
  verifier's `h_V(q) − Δ'·ũ`, `Bridge.voleHash_complete`): `upush_resp`;
* H2, grinding: both sample `(ctr, Δ)` as the first accepted `H₂³` answer (`firstHit`, the law of
  `Grinding.lean`'s `IsFirstHit`: `firstHit_spec`).

**`proveIdeal_close`**: `Close 0 (proveIdeal Hs T st w) (simulate st.params)`. With dedicated
label rows the label offset `Θ` (the tape's `θ`) is moreover uniform and independent of the
proof (`proveIdeal_theta_close`), so a guess of `Θ` from the proof, such as an `H₅` query at a
sibling label (`LabelRows.query_hits_sibling_iff_labelRows`), is right with probability exactly
`2⁻¹²⁸` (`prove_guess_theta`).

Hypotheses (deterministic): the statement's evaluator is a system of degree `≤ d`, `1 ≤ d`, that
the witness satisfies (`hsat`) for every `chal1` and combination (so not PomFRIT, whose instance
depends on `chal1`); `N_MASK ≤ 32`; the CRT certificate `maskInvOk T` (proved for `CrtGen.tables`);
correct interpolation (`InterpOk d`).
-/

open Finset Polynomial

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.EndToEnd
open VoleMole.Privacy

/-! ## Field elements as bytes -/

/-- `k` field elements as `16 k` bytes (`gfsToBytes`). -/
def gfsBytes (k : ℕ) (y : Fin k → GF128) : Bytes (16 * k) :=
  blk (16 * k) (Prover.gfsToBytes (Array.ofFn y))

lemma gfsBytes_injective (k : ℕ) : Function.Injective (gfsBytes k) := by
  intro y y' h
  funext i
  have h1 := congrArg ba h
  rw [gfsBytes, gfsBytes, ba_blk_of_size (by rw [gfsToBytes_size]; simp),
    ba_blk_of_size (by rw [gfsToBytes_size]; simp)] at h1
  have := congrArg (fun b => gfOfBytes b (16 * i)) h1
  rw [gfOfBytes_gfsToBytes _ (by simp), gfOfBytes_gfsToBytes _ (by simp)] at this
  simpa using this

/-- `k` field elements are `16 k` bytes. -/
noncomputable def gfsBytesEquiv (k : ℕ) : (Fin k → GF128) ≃ Bytes (16 * k) :=
  Equiv.ofBijective (gfsBytes k) ((Fintype.bijective_iff_injective_and_card _).2
    ⟨gfsBytes_injective k, by
      rw [Fintype.card_fun, Fintype.card_fun, GF128.card_eq, Prob.card_uint8, Fintype.card_fin,
        Fintype.card_fin, ← pow_mul, ← pow_mul]
      ring_nf⟩)

/-! ## The responses (H7) -/

section Resp

variable {n : ℕ}

/-- **The KOS and QuickSilver responses are uniform.** For any hash `G` of the QuickSilver masks
`uq` (the KOS hash of the rows and of `uq`), any unmasked QuickSilver coefficients `H y` that may
depend on the KOS response `y` (through `chal2`), any `q` and `Δ`: the map from the masks
`(uq, uk)` to `(ã, ũ) = (qsResponse (H ũ) q Δ uq, uk + G uq)` pushes uniform to uniform. -/
theorem upush_resp (G : (Fin n → GF128) → Fin 4 → GF128) (H : (Fin 4 → GF128) → Fin n → GF128)
    (q : Fin n → GF128) (Δ : GF128) :
    UPush (fun x : (Fin n → GF128) × (Fin 4 → GF128) =>
      (qsResponse (H (x.2 + G x.1)) q Δ x.1, x.2 + G x.1)) := by
  have h1 : UPush (fun x : (Fin n → GF128) × (Fin 4 → GF128) => (x.1, x.2 + G x.1)) :=
    upush_shear (g := fun uq uk => uk + G uq) fun uq => upush_equiv (Equiv.addRight (G uq))
  have h2 : UPush (fun x : (Fin n → GF128) × (Fin 4 → GF128) =>
      (qsResponse (H x.2) q Δ x.1, x.2)) :=
    upush_shear' (g := fun y uq => qsResponse (H y) q Δ uq) fun y =>
      upush_equiv (qsEquiv (H y) q Δ)
  exact (h1.comp h2).congr fun _ => rfl

end Resp

/-! ## The VOLE check, with arbitrary rows of `u` -/

/-- `Bridge.voleHash_complete` with the rows of `u` given as field elements (`0`/`1`). -/
theorem voleHash_complete' (p : Params) (c1 : ByteArray)
    (vRows vMask uMask rowsQ maskQ uRows : Array W128) (Δ : GF128) (z z' : ByteArray)
    (hrs : rowsQ.size = p.correctionRows) (hvs : vRows.size = p.correctionRows)
    (hus : uRows.size = p.correctionRows)
    (hmq : maskQ.size = p.nMask) (hmv : vMask.size = p.nMask) (hmu : uMask.size = p.nMask)
    (hrows : ∀ r < p.correctionRows, rowsQ[r]!.toGF = vRows[r]!.toGF + uRows[r]!.toGF * Δ)
    (hmask : ∀ m < p.nMask, maskQ[m]!.toGF = vMask[m]!.toGF + uMask[m]!.toGF * Δ) :
    voleHashReceiver p c1 rowsQ maskQ Δ (Prover.gfsToBytes (voleHashReceiver p c1 uRows uMask 0 z)) =
      voleHashReceiver p c1 vRows vMask 0 z' := by
  set d := p.qsDegree
  have hnm : d - 1 + 4 ≤ p.nMask := by simp only [Params.nMask, d]; omega
  have hxs : (rowsQ.map (·.toGF) ++ (maskQ.extract 0 (d - 1)).map (·.toGF)).toList =
      List.zipWith (fun x y => x + Δ * y)
        (vRows.map (·.toGF) ++ (vMask.extract 0 (d - 1)).map (·.toGF)).toList
        (uRows.map (·.toGF) ++ (uMask.extract 0 (d - 1)).map (·.toGF)).toList := by
    rw [hashed_toList, hashed_toList, hashed_toList]
    apply List.ext_getElem
    · simp [hrs, hvs, hmq, hmv, hmu, hus]
    intro k h1 h2
    simp only [List.getElem_zipWith]
    by_cases hk : k < p.correctionRows
    · have e := hrows k hk
      rw [getElem!_pos rowsQ k (by omega), getElem!_pos vRows k (by omega),
        getElem!_pos uRows k (by omega)] at e
      simp only [List.getElem_append, List.length_map, Array.length_toList, hrs, hvs, hus, hk,
        ↓reduceDIte, List.getElem_map, Array.getElem_toList]
      rw [e]; ring
    · have hk1 : k - p.correctionRows < d - 1 := by
        simp [hrs, hmq] at h1; omega
      have e := hmask (k - p.correctionRows) (by omega)
      rw [getElem!_pos maskQ _ (by omega), getElem!_pos vMask _ (by omega),
        getElem!_pos uMask _ (by omega)] at e
      simp only [List.getElem_append, List.length_map, Array.length_toList, hrs, hvs, hus, hk,
        ↓reduceDIte, List.getElem_map, List.getElem_take, Array.getElem_toList]
      rw [e]; ring
  have hab : (vRows.map (·.toGF) ++ (vMask.extract 0 (d - 1)).map (·.toGF)).size =
      (uRows.map (·.toGF) ++ (uMask.extract 0 (d - 1)).map (·.toGF)).size := by
    simp [hvs, hmv, hmu, hus]
  have hU : ∀ i < 4,
      gfOfBytes (Prover.gfsToBytes (voleHashReceiver p c1 uRows uMask 0 z)) (16 * i) =
      (voleHashReceiver p c1 uRows uMask 0 z)[i]! := fun i hi =>
    gfOfBytes_gfsToBytes _ (by rw [voleHashReceiver_size]; exact hi)
  apply Array.ext
  · rw [voleHashReceiver_size, voleHashReceiver_size]
  intro i h1 h2
  have hi : i < 4 := by rwa [voleHashReceiver_size] at h1
  rw [← getElem!_pos _ i h1, ← getElem!_pos _ i h2]
  obtain ⟨i, rfl⟩ : ∃ j : Fin 4, (j : ℕ) = i := ⟨⟨i, hi⟩, rfl⟩
  rw [voleHashReceiver_get, voleHashReceiver_get, hU i i.isLt, voleHashReceiver_get,
    horner_lin _ Δ _ _ _ hab hxs, horner_lin _ Δ _ _ _ hab hxs, hmask _ (by omega)]
  have h2 : ∀ y : GF128, y + y = 0 := fun y => CharTwo.add_self_eq_zero y
  linear_combination Δ * h2 (uMask[d - 1 + ↑i]!.toGF +
    horner (![gfOfBytes c1 80, gfOfBytes c1 96, gfOfBytes c1 112, ⟨W128.word c1 128, 0⟩] i)
      (uRows.map (·.toGF) ++ (uMask.extract 0 (d - 1)).map (·.toGF)) +
    horner (gfOfBytes c1 64) (uRows.map (·.toGF) ++ (uMask.extract 0 (d - 1)).map (·.toGF)) *
      gfOfBytes c1 (16 * ↑i))

/-! ## The rest of the run, explicitly -/

@[simp] lemma toGF_ofGF (a : GF128) : (Prover.W128.ofGF a).toGF = a := rfl

/-- Field elements as the `u_mask` array. -/
def arrU {k : ℕ} (U : Fin k → GF128) : Array W128 :=
  (Array.range k).map fun m => if h : m < k then Prover.W128.ofGF (U ⟨m, h⟩) else W128.zero

lemma arrU_get {k : ℕ} (U : Fin k → GF128) {m : ℕ} (hm : m < k) : (arrU U)[m]!.toGF = U ⟨m, hm⟩ := by
  rw [arrU, getElem!_range_map _ _ hm]; simp [hm]

lemma arrU_size {k : ℕ} (U : Fin k → GF128) : (arrU U).size = k := by simp [arrU]

section Tail

variable (Hs : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray) (s : Shared) (ctr : ℕ)
  (delta : Bytes 16)

/-- `chal2`, with `h_V` as the verifier recomputes it from `ũ` (`Bridge.voleHash_complete`). -/
def tC2 (c cmult : ByteArray) (ut : Array GF128) (d : ByteArray) : ByteArray :=
  let c1 := tC1 Hs st s ctr delta c cmult
  let crt := tCrt Hs T st s delta c cmult
  chal2 Hs { params := st.params, bytes := Prover.assemble st.params (tF1 s ctr delta c cmult ut d) }
    c1 (voleHashReceiver st.params c1 crt.rows crt.qMask (tDL T delta) (Prover.gfsToBytes ut))
    (st.muDelayed Hs c1) st.binder2

/-- The QuickSilver proof `ã`, for the system `cs`. -/
noncomputable def tAt (cs : ByteArray → ByteArray → System GF128) (c cmult : ByteArray)
    (ubits : Array Bool) (uMask : Array W128) (d : ByteArray) : Array GF128 :=
  let ut := tUt Hs st s ctr delta c cmult ubits uMask
  let c2 := tC2 Hs T st s ctr delta c cmult ut d
  (Array.range (st.params.qsDegree - 1)).map fun i =>
    (qsPoly st.params c2 (cs (tC1 Hs st s ctr delta c cmult) (st.combBytes Hs c2))
      (tVRows Hs T st s delta c cmult ubits) (tVMask Hs T st s delta c cmult uMask) uMask w).coeff
      (i + 1)

/-- **The rest of the ideal prover's run, explicitly**: the proof with `ũ = tUt` and the
QuickSilver coefficients `ã = tAt`, for a witness satisfying the system. -/
theorem idealTail_eq (cs : ByteArray → ByteArray → System GF128)
    (hvals : ∀ c1 lb x, st.values c1 lb x = (cs c1 lb).values x)
    (hdeg : ∀ c1 lb, ∀ e ∈ cs c1 lb, e.degree ≤ st.params.qsDegree)
    (hd : 1 ≤ st.params.qsDegree) (hd' : st.params.qsDegree + 1 < 2 ^ 64)
    (hI : InterpOk st.params.qsDegree) (hsat : ∀ c1 lb, (cs c1 lb).Holds (wSlope st.params w))
    (c cmult : ByteArray) (uMask : Array W128) (ubits : Array Bool) (d : ByteArray)
    (hum : uMask.size = st.params.nMask) :
    idealTail Hs T st w s ctr delta c cmult uMask ubits d =
      .ok (Prover.assemble st.params
        { tF1 s ctr delta c cmult (tUt Hs st s ctr delta c cmult ubits uMask) d with
          qsProof := Prover.gfsToBytes (tAt Hs T st w s ctr delta cs c cmult ubits uMask d),
          delta := ba delta, ctr := ctrBytes ctr, opening := (pubOf Hs st s delta).opening }) := by
  set ut := tUt Hs st s ctr delta c cmult ubits uMask
  set crt := tCrt Hs T st s delta c cmult
  set vRows := tVRows Hs T st s delta c cmult ubits
  set vMask := tVMask Hs T st s delta c cmult uMask
  set c1 := tC1 Hs st s ctr delta c cmult
  -- `h_V` is the verifier's recomputation from `ũ`.
  have hrs : crt.rows.size = st.params.correctionRows := by
    simp [crt, tCrt, crtReconstructAt, crtReconstructWith]
  have hms : crt.qMask.size = st.params.nMask := by
    simp [crt, tCrt, crtReconstructAt, crtReconstructWith]
  have h2 : ∀ y : GF128, y + y = 0 := fun y => CharTwo.add_self_eq_zero y
  have hV : voleHashReceiver st.params c1 vRows vMask 0 (Prover.zeros 64) =
      voleHashReceiver st.params c1 crt.rows crt.qMask (tDL T delta) (Prover.gfsToBytes ut) := by
    refine (voleHash_complete' st.params c1 vRows vMask uMask crt.rows crt.qMask (tURows st ubits)
      (tDL T delta) _ _ hrs (by simp [vRows, tVRows]) (by simp [tURows]) hms
      (by simp [vMask, tVMask]) hum (fun r hr => ?_) (fun m hm => ?_)).symm
    · simp only [vRows, tVRows, tURows, getElem!_range_map _ _ hr]
      cases ubits[r]!
      · show _ = (crt.rows[r]!.toGF + 0) + 0 * tDL T delta
        rw [zero_mul, add_zero, add_zero]
      · show _ = (crt.rows[r]!.toGF + tDL T delta) + 1 * tDL T delta
        rw [one_mul, add_assoc, h2, add_zero]
    · simp only [vMask, tVMask, getElem!_range_map _ _ hm]
      show _ = (crt.qMask[m]!.toGF + uMask[m]!.toGF * tDL T delta) + uMask[m]!.toGF * tDL T delta
      rw [add_assoc, h2, add_zero]
  have h0 : ∀ i, gfOfBytes (Proof.mk st.params (Prover.assemble st.params
      (tF1 s ctr delta c cmult ut d))).qsProof (16 * i) = 0 := by
    intro i
    rw [(fields_assemble st.params _).2.2.2.2.1]
    show gfOfBytes (Prover.fit ByteArray.empty _) _ = 0
    rw [fit_empty, gfOfBytes_zeros]
  have hq := qsProve_eq (Proof.mk st.params (Prover.assemble st.params
      (tF1 s ctr delta c cmult ut d)))
    (tC2 Hs T st s ctr delta c cmult ut d)
    (st.values c1 (st.combBytes Hs (tC2 Hs T st s ctr delta c cmult ut d))) vRows vMask uMask w
    (cs c1 (st.combBytes Hs (tC2 Hs T st s ctr delta c cmult ut d))) (hvals _ _) (hdeg _ _) hd hd'
    h0 hI (hsat _ _)
  have hc2 : chal2 Hs (Proof.mk st.params (Prover.assemble st.params (tF1 s ctr delta c cmult ut d)))
      c1 (voleHashReceiver st.params c1 vRows vMask 0 (Prover.zeros 64)) (st.muDelayed Hs c1)
      st.binder2 = tC2 Hs T st s ctr delta c cmult ut d := by
    rw [hV]; rfl
  unfold idealTail
  simp only []
  rw [hc2, hq]
  rfl

end Tail

/-! ## The masks: `ũ` and `ã` as functions of `u_mask` (H7) -/

section Masks

variable (Hs : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray) (s : Shared) (ctr : ℕ)
  (delta : Bytes 16)

/-- The `d − 1` QuickSilver masks and the 4 VOLE-check masks, as one `u_mask`. -/
def splitE (p : Params) :
    (Fin (p.qsDegree - 1) → GF128) × (Fin 4 → GF128) ≃ (Fin p.nMask → GF128) where
  toFun x m := if h : m.val < p.qsDegree - 1 then x.1 ⟨m, h⟩
    else x.2 ⟨m - (p.qsDegree - 1), by have := m.isLt; simp only [Params.nMask] at this; omega⟩
  invFun U := (fun k => U ⟨k, by simp only [Params.nMask]; omega⟩,
    fun i => U ⟨p.qsDegree - 1 + i, by simp only [Params.nMask]; omega⟩)
  left_inv x := by
    ext k
    · simp [k.isLt]
    · simp
  right_inv U := by
    funext m
    by_cases h : m.val < p.qsDegree - 1
    · simp [h]
    · simp only [h, dite_false]
      congr 1; ext; simp only; omega

lemma splitE_lo (p : Params) (x : (Fin (p.qsDegree - 1) → GF128) × (Fin 4 → GF128)) {k : ℕ}
    (hk : k < p.qsDegree - 1) : splitE p x ⟨k, by simp only [Params.nMask]; omega⟩ = x.1 ⟨k, hk⟩ := by
  simp [splitE, hk]

lemma splitE_hi (p : Params) (x : (Fin (p.qsDegree - 1) → GF128) × (Fin 4 → GF128)) (i : Fin 4) :
    splitE p x ⟨p.qsDegree - 1 + i, by simp only [Params.nMask]; omega⟩ = x.2 i := by
  simp [splitE]

/-- The prefix of `u_mask` that the VOLE check hashes depends on the QuickSilver masks only. -/
lemma arrU_extract (p : Params) (x y : (Fin (p.qsDegree - 1) → GF128) × (Fin 4 → GF128))
    (h : x.1 = y.1) :
    (arrU (splitE p x)).extract 0 (p.qsDegree - 1) = (arrU (splitE p y)).extract 0 (p.qsDegree - 1) := by
  apply Array.ext
  · simp [arrU_size]
  intro k h1 h2
  have hk : k < p.qsDegree - 1 := by simp [arrU_size] at h1; omega
  have hk' : k < p.nMask := by simp only [Params.nMask]; omega
  simp only [Array.getElem_extract, Nat.zero_add]
  simp only [arrU, Array.getElem_map, Array.getElem_range, hk', dite_true]
  rw [splitE_lo p x hk, splitE_lo p y hk, h]

variable (cs : ByteArray → ByteArray → System GF128) (c cmult : ByteArray) (ubits : Array Bool)
  (d : ByteArray)

/-- `ũ` as a function. -/
def utF (U : Fin st.params.nMask → GF128) (i : Fin 4) : GF128 :=
  (tUt Hs st s ctr delta c cmult ubits (arrU U))[(i : ℕ)]!

/-- The VOLE-check hash of the QuickSilver masks (`ũ` with the direct masks zero). -/
def kosG (uq : Fin (st.params.qsDegree - 1) → GF128) (i : Fin 4) : GF128 :=
  utF Hs st s ctr delta c cmult ubits (splitE st.params (uq, 0)) i

/-- **`ũ` = the 4 direct masks + a hash of the others.** -/
lemma utF_split (x : (Fin (st.params.qsDegree - 1) → GF128) × (Fin 4 → GF128)) :
    utF Hs st s ctr delta c cmult ubits (splitE st.params x) =
      x.2 + kosG Hs st s ctr delta c cmult ubits x.1 := by
  funext i
  simp only [utF, kosG, tUt, Pi.add_apply]
  rw [voleHashReceiver_get, voleHashReceiver_get,
    arrU_extract st.params x (x.1, 0) rfl]
  have hi : st.params.qsDegree - 1 + i < st.params.nMask := by simp only [Params.nMask]; omega
  rw [arrU_get _ hi, arrU_get _ hi, splitE_hi, splitE_hi]
  simp only [Pi.zero_apply, zero_mul, add_zero, zero_add]
  ring

lemma tUt_eq (U : Fin st.params.nMask → GF128) :
    tUt Hs st s ctr delta c cmult ubits (arrU U) = Array.ofFn (utF Hs st s ctr delta c cmult ubits U) := by
  apply Array.ext
  · simp [tUt, voleHashReceiver_size]
  intro i h1 h2
  have hi : i < 4 := by simpa [tUt, voleHashReceiver_size] using h1
  simp only [Array.getElem_ofFn, utF]
  rw [getElem!_pos _ i h1]

/-- The unmasked QuickSilver coefficients, from `ũ` (through `chal2`). -/
noncomputable def qsH (y : Fin 4 → GF128) (k : Fin (st.params.qsDegree - 1)) : GF128 :=
  let c2 := tC2 Hs T st s ctr delta c cmult (Array.ofFn y) d
  (sysCheckPoly (keyPoly st.params (tVRows Hs T st s delta c cmult ubits) w)
    (cs (tC1 Hs st s ctr delta c cmult) (st.combBytes Hs c2)) st.params.qsDegree
    (Seed.zkCoeff _ (gfOfBytes c2 0) (gfOfBytes c2 16) (gfOfBytes c2 32) ⟨W128.word c2 48, 0⟩)
    0).coeff (k + 1)

/-- The verifier's masks `q_mask` on the QuickSilver masks. -/
def qbar (k : Fin (st.params.qsDegree - 1)) : GF128 := (tCrt Hs T st s delta c cmult).qMask[(k : ℕ)]!.toGF

/-- **`ã` is the QuickSilver response** of the QuickSilver masks, with coefficients that depend on
the masks only through `ũ`. -/
lemma tAt_get (x : (Fin (st.params.qsDegree - 1) → GF128) × (Fin 4 → GF128))
    (k : Fin (st.params.qsDegree - 1)) :
    (tAt Hs T st w s ctr delta cs c cmult ubits (arrU (splitE st.params x)) d)[(k : ℕ)]! =
      qsResponse (qsH Hs T st w s ctr delta cs c cmult ubits d
          (utF Hs st s ctr delta c cmult ubits (splitE st.params x)))
        (qbar Hs T st s delta c cmult) (tDL T delta) x.1 k := by
  have hk := k.isLt
  have hd : (k : ℕ) + 1 ≤ st.params.qsDegree - 1 := by omega
  have hkm : (k : ℕ) < st.params.nMask := by simp only [Params.nMask]; omega
  simp only [tAt]
  rw [getElem!_range_map _ _ hk, tUt_eq, qsPoly, sysCheckPoly_add, coeff_add,
    maskPoly_coeff _ _ _ (by omega) hd, Nat.add_sub_cancel, arrU_get _ hkm, splitE_lo _ _ hk]
  simp only [qsResponse, nextVal, qsH, qbar]
  by_cases h1 : (k : ℕ) + 1 < st.params.qsDegree - 1
  · have hk1 : (k : ℕ) + 1 < st.params.nMask := by simp only [Params.nMask]; omega
    simp only [h1, ↓reduceIte, dite_true, tVMask, getElem!_range_map _ _ hk1, arrU_get _ hk1,
      splitE_lo _ _ h1]
    rw [toGF_ofGF, sub_eq_add_neg, ← neg_mul, CharTwo.neg_eq]
    ring
  · simp only [h1, ↓reduceIte, dite_false]
    ring

end Masks

/-! ## The responses are uniform, for every value of the rest -/

section Resp2

variable (Hs : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray) (s : Shared) (ctr : ℕ)
  (delta : Bytes 16) (cs : ByteArray → ByteArray → System GF128) (c cmult : ByteArray)
  (ubits : Array Bool) (d : ByteArray)

/-- The two response fields, `ũ` and `ã`, as bytes. -/
noncomputable def respB (U : Fin st.params.nMask → GF128) :
    Bytes 64 × Bytes (16 * (st.params.qsDegree - 1)) :=
  (gfsBytes 4 (utF Hs st s ctr delta c cmult ubits U),
   gfsBytes (st.params.qsDegree - 1) fun k =>
     (tAt Hs T st w s ctr delta cs c cmult ubits (arrU U) d)[(k : ℕ)]!)

/-- **H7**: uniform `u_mask` gives uniform `(ũ, ã)`, for every value of the corrections, `c_mult`,
the bits of `u` and `d`. -/
theorem upush_respB : UPush (respB Hs T st w s ctr delta cs c cmult ubits d) := by
  have key : ∀ x, respB Hs T st w s ctr delta cs c cmult ubits d (splitE st.params x) =
      (gfsBytes 4 (x.2 + kosG Hs st s ctr delta c cmult ubits x.1),
       gfsBytes (st.params.qsDegree - 1) (qsResponse
         (qsH Hs T st w s ctr delta cs c cmult ubits d
           (x.2 + kosG Hs st s ctr delta c cmult ubits x.1))
         (qbar Hs T st s delta c cmult) (tDL T delta) x.1)) := by
    intro x
    unfold respB
    rw [utF_split]
    refine Prod.ext rfl (congrArg (gfsBytes _) (funext fun k => ?_))
    rw [tAt_get, utF_split]
  have h1 := upush_resp (kosG Hs st s ctr delta c cmult ubits)
    (qsH Hs T st w s ctr delta cs c cmult ubits d) (qbar Hs T st s delta c cmult) (tDL T delta)
  let E : (Fin (st.params.qsDegree - 1) → GF128) × (Fin 4 → GF128) ≃
      Bytes (16 * 4) × Bytes (16 * (st.params.qsDegree - 1)) :=
    (Equiv.prodComm _ _).trans
      (Equiv.prodCongr (gfsBytesEquiv 4) (gfsBytesEquiv (st.params.qsDegree - 1)))
  have h2 : UPush (fun y : (Fin (st.params.qsDegree - 1) → GF128) × (Fin 4 → GF128) =>
      (gfsBytes 4 y.2, gfsBytes (st.params.qsDegree - 1) y.1)) :=
    (upush_equiv E).congr fun y => by
      simp only [E, Equiv.trans_apply, Equiv.prodComm_apply, Equiv.prodCongr_apply, Prod.map,
        gfsBytesEquiv, Equiv.ofBijective_apply, Prod.fst_swap, Prod.snd_swap]
  have h3 := (upush_equiv (splitE st.params).symm).comp (h1.comp h2)
  refine h3.congr fun U => ?_
  have := key ((splitE st.params).symm U)
  rw [Equiv.apply_symm_apply] at this
  rw [this]
  simp only [Function.comp_apply]

end Resp2

/-! ## The masks from their pads -/

/-- `u_mask` from the mask pads. -/
def uOfM (T : CrtTables) {p : Params} (m : (Fin BAVC.tau → Bytes p.nMask) × Bytes p.nMask) :
    Fin p.nMask → GF128 :=
  fun j => crtVal T (fun i => m.1 i j) (m.2 j)

theorem upush_uOfM {T : CrtTables} (hT : maskInvOk T = true) (p : Params) :
    UPush (uOfM T (p := p)) := by
  let e : (Fin BAVC.tau → Bytes p.nMask) × Bytes p.nMask ≃
      (Fin p.nMask → (Fin BAVC.tau → UInt8) × UInt8) :=
    { toFun := fun m j => (fun i => m.1 i j, m.2 j)
      invFun := fun y => (fun i j => (y j).1 i, fun j => (y j).2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h := upush_pi (A := fun _ : Fin p.nMask => (Fin BAVC.tau → UInt8) × UInt8)
    (f := fun _ z => crtVal T z.1 z.2) fun _ => balanced_crtVal hT
  exact ((upush_equiv e).comp h).congr fun _ => rfl

lemma uMaskArr_eq (T : CrtTables) {p : Params} (t : Pads p) :
    uMaskArr T t = arrU (uOfM T (t.2.2.2.1, t.2.2.2.2.2.1)) := by
  refine Array.map_congr_left fun m hm => ?_
  have hm' := Array.mem_range.1 hm
  simp only [hm', dite_true, uOfM, crtVal, get!_ba _ hm']
  rfl

/-! ## The row pads: corrections, `d` and `Θ` (H5) -/

/-- The row pads: `u0w`, `θ`, the corrected rows of `u^{(i)}`, the remaining rows. -/
abbrev RowPads (p : Params) :=
  Bytes p.witnessBytes × Bytes (labelBytes p) × (Fin (BAVC.tau - 1) → Bytes p.correctionBytes) ×
    (Fin BAVC.tau → Bytes (restBytes p))

/-- The mask pads. -/
abbrev MaskPads (p : Params) := (Fin BAVC.tau → Bytes p.nMask) × Bytes p.nMask

/-- The pads from their three parts. -/
def padsOf {p : Params} (a : RowPads p) (m : MaskPads p) (c : Fin 312 → Bytes 4) : Pads p :=
  (a.1, a.2.1, a.2.2.1, m.1, a.2.2.2, m.2, c)

/-- The pads are their three parts. -/
def padsE (p : Params) : Pads p ≃ RowPads p × (MaskPads p × (Fin 312 → Bytes 4)) where
  toFun t := ((t.1, t.2.1, t.2.2.1, t.2.2.2.2.1), ((t.2.2.2.1, t.2.2.2.2.2.1), t.2.2.2.2.2.2))
  invFun x := padsOf x.1 x.2.1 x.2.2
  left_inv _ := rfl
  right_inv _ := rfl

lemma U0_get {p : Params} (u0w : Bytes p.witnessBytes) (θ : Bytes (labelBytes p)) {k : ℕ}
    (hk : k < p.correctionBytes) :
    (ba u0w ++ ba θ).get! k =
      if h : k < p.witnessBytes then u0w ⟨k, h⟩ else θ ⟨k - p.witnessBytes, by
        have := labelBytes_add p; omega⟩ := by
  rw [get!_append, size_ba]
  split_ifs with h
  · exact get!_ba _ h
  · exact get!_ba _ _

/-- **H5 on the corrected rows**: `(u0w, θ, u^{(i)}) ↦ (c, d, Θ)` is a bijection, for every `w`. -/
def rowsEquiv (p : Params) (w : ByteArray) :
    Bytes p.witnessBytes × Bytes (labelBytes p) × (Fin (BAVC.tau - 1) → Bytes p.correctionBytes) ≃
      Bytes (16 * p.correctionBytes) × Bytes p.witnessBytes × Bytes (labelBytes p) where
  toFun x := (fun j => (ba x.1 ++ ba x.2.1).get! (j % p.correctionBytes) ^^^
      (ba (x.2.2 ⟨j / p.correctionBytes, by
        have := j.isLt; rw [tau_sub_one]; exact Nat.div_lt_of_lt_mul (by linarith)⟩)).get!
        (j % p.correctionBytes),
    fun k => x.1 k ^^^ w.get! k, x.2.1)
  invFun y :=
    let u0w : Bytes p.witnessBytes := fun k => y.2.1 k ^^^ w.get! k
    (u0w, y.2.2, fun i k => y.1 ⟨i * p.correctionBytes + k, by
      have hi : i.val + 1 ≤ 16 := by have := i.isLt; have h17 : BAVC.tau = 17 := rfl; omega
      have h1 := Nat.mul_le_mul_right p.correctionBytes hi
      have := k.isLt
      rw [Nat.succ_mul] at h1
      omega⟩ ^^^
        (ba u0w ++ ba y.2.2).get! k)
  left_inv x := by
    obtain ⟨u0w, θ, ui⟩ := x
    have hu : (fun k => (u0w k ^^^ w.get! k) ^^^ w.get! k) = u0w := by
      funext k; rw [UInt8.xor_assoc, UInt8.xor_self, UInt8.xor_zero]
    simp only [hu]
    refine Prod.ext rfl (Prod.ext rfl (funext fun i => funext fun k => ?_))
    have hcb : 0 < p.correctionBytes := lt_of_le_of_lt (Nat.zero_le _) k.isLt
    have e1 : (i.val * p.correctionBytes + k) % p.correctionBytes = k := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt k.isLt]
    have e2 : (i.val * p.correctionBytes + k) / p.correctionBytes = i := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hcb, Nat.div_eq_of_lt k.isLt, Nat.zero_add]
    simp only [e1]
    rw [UInt8.xor_comm, ← UInt8.xor_assoc, UInt8.xor_self, UInt8.zero_xor]
    have : (⟨(i.val * p.correctionBytes + k) / p.correctionBytes, by omega⟩ :
        Fin (BAVC.tau - 1)) = i := Fin.ext e2
    rw [get!_ba _ k.isLt, this]
  right_inv y := by
    obtain ⟨c, d, θ⟩ := y
    have hu : (fun k => (d k ^^^ w.get! k) ^^^ w.get! k) = d := by
      funext k; rw [UInt8.xor_assoc, UInt8.xor_self, UInt8.xor_zero]
    refine Prod.ext (funext fun j => ?_) (Prod.ext hu rfl)
    have hcb : 0 < p.correctionBytes := Nat.pos_of_ne_zero fun h => by have := j.isLt; omega
    have hj : j.val % p.correctionBytes < p.correctionBytes := Nat.mod_lt _ hcb
    simp only
    rw [get!_ba _ hj]
    simp only
    have e : (⟨j.val / p.correctionBytes * p.correctionBytes + j.val % p.correctionBytes, by
        rw [Nat.div_add_mod']; exact j.isLt⟩ : Fin (16 * p.correctionBytes)) = j :=
      Fin.ext (Nat.div_add_mod' _ _)
    rw [e]
    rw [UInt8.xor_comm, UInt8.xor_assoc, UInt8.xor_self, UInt8.xor_zero]

/-! ## The ideal prover's proof fields -/

section Main

variable (Hs : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)
  (cs : ByteArray → ByteArray → System GF128)

/-- The ideal prover's `c_mult`, as a block. -/
def cmB (s : Shared) (delta : Bytes 16) (t : Pads st.params) :
    Bytes (st.params.nMask * st.params.nMultBytes) :=
  blk _ (cmultIdeal Hs T st (pubOf Hs st s delta) delta
    (qcolsOf st (pubOf Hs st s delta) delta (ba (corrB t))) (usOf st.params t)[0]! (uMaskArr T t)
    t.2.2.2.2.2.2)

/-- **The ideal prover's proof fields**, from its pads, and the label offset `Θ`. -/
noncomputable def fieldsOf (s : Shared) (ctr : ℕ) (delta : Bytes 16) (t : Pads st.params) :
    SimFields st.params × Bytes (labelBytes st.params) :=
  let r := respB Hs T st w s ctr delta cs (ba (corrB t)) (ba (cmB Hs T st s delta t))
    ((Array.range st.params.correctionRows).map (ubitF t)) (ba (dB w t))
    (uOfM T (t.2.2.2.1, t.2.2.2.2.2.1))
  ((corrB t, cmB Hs T st s delta t, r.1, dB w t, r.2), t.2.1)

/-- The proof with given fields (the simulator's assembly). -/
def simAssemble (p : Params) (s : Shared) (ctr : ℕ) (delta : Bytes 16) (f : SimFields p) :
    ByteArray :=
  Prover.assemble p { publicFields s ctr delta with
    corrections := ba f.1, cmult := ba f.2.1, voleCheck := ba f.2.2.1,
    correction := ba f.2.2.2.1, qsProof := ba f.2.2.2.2 }

lemma gfsToBytes_ofFn {k : ℕ} (y : Fin k → GF128) :
    Prover.gfsToBytes (Array.ofFn y) = ba (gfsBytes k y) := by
  rw [gfsBytes, ba_blk_of_size (by rw [gfsToBytes_size]; simp)]

lemma cmultIdeal_size (P : Pub) (delta : Bytes 16) (qcols : Array (Array UInt64))
    (u : Array UInt64) (uMask : Array W128) (sib : Fin 312 → Bytes 4) :
    (cmultIdeal Hs T st P delta qcols u uMask sib).size = st.params.nMask * st.params.nMultBytes := by
  rw [cmultIdeal, cMultOf_eq, size_ba]

/-- **The ideal prover's run, as its fields**: for a witness that satisfies the system, the run
after the grinding outcome is the simulator's assembly of `fieldsOf`. -/
theorem idealCore_fields
    (hvals : ∀ c1 lb x, st.values c1 lb x = (cs c1 lb).values x)
    (hdeg : ∀ c1 lb, ∀ e ∈ cs c1 lb, e.degree ≤ st.params.qsDegree)
    (hd : 1 ≤ st.params.qsDegree) (hd' : st.params.qsDegree + 1 < 2 ^ 64)
    (hI : InterpOk st.params.qsDegree) (hsat : ∀ c1 lb, (cs c1 lb).Holds (wSlope st.params w))
    (s : Shared) (ctr : ℕ) (delta : Bytes 16) (t : Pads st.params) :
    idealCore Hs T st w s ctr delta t =
      .ok (simAssemble st.params s ctr delta (fieldsOf Hs T st w cs s ctr delta t).1) := by
  rw [idealCore_eq, uMaskArr_eq]
  have hcm : cmultIdeal Hs T st (pubOf Hs st s delta) delta
      (qcolsOf st (pubOf Hs st s delta) delta (ba (corrB t))) (usOf st.params t)[0]!
      (arrU (uOfM T (t.2.2.2.1, t.2.2.2.2.2.1))) t.2.2.2.2.2.2 = ba (cmB Hs T st s delta t) := by
    rw [cmB, uMaskArr_eq, ba_blk_of_size (cmultIdeal_size _ _ _ _ _ _ _ _ _)]
  rw [hcm, idealTail_eq Hs T st w s ctr delta cs hvals hdeg hd hd' hI hsat _ _ _ _ _
    (arrU_size _)]
  simp only [fieldsOf, simAssemble, respB, tF1, tF0, Except.ok.injEq]
  rw [tUt_eq, gfsToBytes_ofFn]
  have hat : Prover.gfsToBytes (tAt Hs T st w s ctr delta cs (ba (corrB t))
      (ba (cmB Hs T st s delta t)) ((Array.range st.params.correctionRows).map (ubitF t))
      (arrU (uOfM T (t.2.2.2.1, t.2.2.2.2.2.1))) (ba (dB w t))) =
      ba (gfsBytes (st.params.qsDegree - 1) fun k => (tAt Hs T st w s ctr delta cs (ba (corrB t))
        (ba (cmB Hs T st s delta t)) ((Array.range st.params.correctionRows).map (ubitF t))
        (arrU (uOfM T (t.2.2.2.1, t.2.2.2.2.2.1))) (ba (dB w t)))[(k : ℕ)]!) := by
    rw [← gfsToBytes_ofFn]
    congr 1
    apply Array.ext
    · simp [tAt]
    intro i h1 h2
    simp only [Array.getElem_ofFn]
    rw [getElem!_pos _ i h1]
  rw [hat]
  rfl

end Main

/-! ## The proof fields are uniform -/

section Uniform

variable (Hs : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)
  (cs : ByteArray → ByteArray → System GF128) (s : Shared) (ctr : ℕ) (delta : Bytes 16)

/-- The pads' default mask and sibling parts (the row-pad functions do not read them). -/
def m0 (p : Params) : MaskPads p := (fun _ _ => 0, fun _ => 0)
def c0 : Fin 312 → Bytes 4 := fun _ _ => 0

/-- The response fields for row pads `a` and `c_mult`. -/
noncomputable def respA (a : RowPads st.params) (cm : Bytes (st.params.nMask * st.params.nMultBytes))
    (U : Fin st.params.nMask → GF128) : Bytes 64 × Bytes (16 * (st.params.qsDegree - 1)) :=
  respB Hs T st w s ctr delta cs (ba (corrB (padsOf a (m0 _) c0))) (ba cm)
    ((Array.range st.params.correctionRows).map (ubitF (padsOf a (m0 _) c0)))
    (ba (dB w (padsOf a (m0 _) c0))) U

lemma cmB_padsOf (a : RowPads st.params) (m : MaskPads st.params) (c : Fin 312 → Bytes 4) :
    cmB Hs T st s delta (padsOf a m c) =
      blk _ (cmultIdeal Hs T st (pubOf Hs st s delta) delta
        (qcolsOf st (pubOf Hs st s delta) delta (ba (corrB (padsOf a m c0))))
        (usOf st.params (padsOf a m c0))[0]! (uMaskArr T (padsOf a m c0)) c) := rfl

/-- **For fixed row pads, `(c_mult, ũ, ã)` is uniform** (H6, §7.4, H7). -/
theorem upush_inner (hT : maskInvOk T = true) (hnm : st.params.nMask ≤ 32) (a : RowPads st.params) :
    UPush (fun mc : MaskPads st.params × (Fin 312 → Bytes 4) =>
      (cmB Hs T st s delta (padsOf a mc.1 mc.2),
        respA Hs T st w cs s ctr delta a (cmB Hs T st s delta (padsOf a mc.1 mc.2)) (uOfM T mc.1))) := by
  have h1 := upush_shear (α := MaskPads st.params) fun m =>
    upush_cmult Hs T st (pubOf Hs st s delta) delta
      (qcolsOf st (pubOf Hs st s delta) delta (ba (corrB (padsOf a m c0))))
      (usOf st.params (padsOf a m c0))[0]! (uMaskArr T (padsOf a m c0)) hnm
  have h2 := UPush.prodMap (upush_uOfM hT st.params)
    (upush_id (α := Bytes (st.params.nMask * st.params.nMultBytes)))
  have h3 := (upush_shear' (α := Fin st.params.nMask → GF128)
    fun cm : Bytes (st.params.nMask * st.params.nMultBytes) =>
    upush_respB Hs T st w s ctr delta cs (ba (corrB (padsOf a (m0 _) c0))) (ba cm)
      ((Array.range st.params.correctionRows).map (ubitF (padsOf a (m0 _) c0)))
      (ba (dB w (padsOf a (m0 _) c0)))).comp (upush_equiv (Equiv.prodComm _ _))
  refine ((h1.comp h2).comp h3).congr fun mc => ?_
  rw [cmB_padsOf]
  rfl

/-- **The row pads give uniform corrections, `d` and `Θ`** (H5). -/
theorem upush_rows :
    UPush (fun a : RowPads st.params =>
      (corrB (padsOf a (m0 _) c0), dB w (padsOf a (m0 _) c0), a.2.1)) := by
  have h1 : UPush (fun a : RowPads st.params => (a.1, a.2.1, a.2.2.1)) := by
    let e : RowPads st.params ≃ (Bytes st.params.witnessBytes × Bytes (labelBytes st.params) ×
        (Fin (BAVC.tau - 1) → Bytes st.params.correctionBytes)) × (Fin BAVC.tau → Bytes (restBytes st.params)) :=
      { toFun := fun a => ((a.1, a.2.1, a.2.2.1), a.2.2.2)
        invFun := fun x => (x.1.1, x.1.2.1, x.1.2.2, x.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact ((upush_equiv e).comp upush_fst).congr fun _ => rfl
  refine (h1.comp (upush_equiv (rowsEquiv st.params w))).congr fun a => ?_
  simp only [Function.comp_apply]
  rfl

/-- **The ideal prover's fields and `Θ` are uniform.** -/
theorem upush_fieldsOf (hT : maskInvOk T = true) (hnm : st.params.nMask ≤ 32) :
    UPush (fieldsOf Hs T st w cs s ctr delta) := by
  have h1 := upush_shear (α := RowPads st.params) fun a =>
    upush_inner Hs T st w cs s ctr delta hT hnm a
  have h2 := UPush.prodMap (upush_rows st w) (upush_id (α := Bytes (st.params.nMask * st.params.nMultBytes) ×
    (Bytes 64 × Bytes (16 * (st.params.qsDegree - 1)))))
  let r : (Bytes (16 * st.params.correctionBytes) × Bytes st.params.witnessBytes ×
      Bytes (labelBytes st.params)) × (Bytes (st.params.nMask * st.params.nMultBytes) ×
      (Bytes 64 × Bytes (16 * (st.params.qsDegree - 1)))) ≃
      SimFields st.params × Bytes (labelBytes st.params) :=
    { toFun := fun x => ((x.1.1, x.2.1, x.2.2.1, x.1.2.1, x.2.2.2), x.1.2.2)
      invFun := fun y => ((y.1.1, y.1.2.2.2.1, y.2), (y.1.2.1, y.1.2.2.1, y.1.2.2.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h3 := ((upush_equiv (padsE st.params)).comp ((h1.comp h2).comp (upush_equiv r)))
  exact h3.congr fun _ => rfl

end Uniform

/-! ## The main theorem -/

section Close

variable (Hs : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)
  (cs : ByteArray → ByteArray → System GF128)

/-- The deterministic hypotheses of the zero-knowledge theorem. -/
structure ZKHyp : Prop where
  hvals : ∀ c1 lb x, st.values c1 lb x = (cs c1 lb).values x
  hdeg : ∀ c1 lb, ∀ e ∈ cs c1 lb, e.degree ≤ st.params.qsDegree
  hd : 1 ≤ st.params.qsDegree
  hd' : st.params.qsDegree + 1 < 2 ^ 64
  hsat : ∀ c1 lb, (cs c1 lb).Holds (wSlope st.params w)
  hw : w.size = st.params.witnessBytes
  hnm : st.params.nMask ≤ 32
  hT : maskInvOk T = true
  hI : InterpOk st.params.qsDegree

lemma upush_theta (p : Params) : UPush (fun t : Pads p => t.2.1) :=
  (upush_snd (α := Bytes p.witnessBytes)).comp upush_fst

/-- **Zero knowledge on the ideal tape, with the label offset.** The ideal-tape prover's proof and
the label offset `Θ` (the tape's `θ`) are distributed as a simulated proof and an independent
uniform `θ`. -/
theorem proveIdeal_theta_close (h : ZKHyp T st w cs) :
    Close 0 (fun t : IdealTape st.params => (proveIdeal Hs T st w t, t.2.2.1))
      (fun x : SimCoins st.params × Bytes (labelBytes st.params) => (simulate st.params x.1, x.2)) := by
  let Y : Shared × (SimFields st.params × Bytes (labelBytes st.params)) →
      Except String ByteArray × Bytes (labelBytes st.params) :=
    fun y => (simulate st.params (y.1, y.2.1), y.2.2)
  have hY : Close 0 (fun x : SimCoins st.params × Bytes (labelBytes st.params) =>
      (simulate st.params x.1, x.2)) Y :=
    (close_equiv (Equiv.prodAssoc _ _ _) Y).congr (fun _ => rfl) fun _ => rfl
  suffices hmain : ∀ s : Shared, Close 0 (fun t : Pads st.params => (proveIdeal Hs T st w (s, t), t.2.1))
      (fun f : SimFields st.params × Bytes (labelBytes st.params) => (simulate st.params (s, f.1), f.2)) by
    have := Close.prod_right (X := fun s (t : Pads st.params) => (proveIdeal Hs T st w (s, t), t.2.1))
      (Y := fun s (f : SimFields st.params × Bytes (labelBytes st.params)) =>
        (simulate st.params (s, f.1), f.2)) hmain
    exact ((this.trans hY.symm).mono (by norm_num)).congr (fun _ => rfl) fun _ => rfl
  intro s
  have hw : (w.size != st.params.witnessBytes) = false := by simp [h.hw]
  rcases hf : firstHit s.2.1 with _ | ⟨ctr, delta⟩
  · -- No accepted grinding answer: both refuse.
    have e1 : ∀ t : Pads st.params, proveIdeal Hs T st w (s, t) = .error "grinding failed" :=
      fun t => by simp [proveIdeal, hw, hf]
    have e2 : ∀ f : SimFields st.params, simulate st.params (s, f) = .error "grinding failed" :=
      fun f => by simp [simulate, hf]
    have h1 := (upush_theta st.params).close fun θ => ((Except.error "grinding failed" :
      Except String ByteArray), θ)
    have h2 := (upush_snd (α := SimFields st.params) (β := Bytes (labelBytes st.params))).close
      fun θ => ((Except.error "grinding failed" : Except String ByteArray), θ)
    exact ((h1.trans h2.symm).mono (by norm_num)).congr (fun t => by rw [e1]) fun f => by rw [e2]
  · -- The grinding outcome `(ctr, Δ)`; then the fields.
    let H : SimFields st.params × Bytes (labelBytes st.params) →
        Except String ByteArray × Bytes (labelBytes st.params) :=
      fun x => (.ok (simAssemble st.params s ctr delta x.1), x.2)
    have e1 : ∀ t : Pads st.params, (proveIdeal Hs T st w (s, t), t.2.1) =
        H (fieldsOf Hs T st w cs s ctr delta t) := by
      intro t
      simp only [proveIdeal, hw, hf, Bool.false_eq_true, ↓reduceIte, H]
      rw [idealCore_fields Hs T st w cs h.hvals h.hdeg h.hd h.hd' h.hI h.hsat]
      rfl
    have e2 : ∀ f : SimFields st.params × Bytes (labelBytes st.params),
        (simulate st.params (s, f.1), f.2) = H f := by
      intro f
      simp only [simulate, hf, H]
      rfl
    exact ((upush_fieldsOf Hs T st w cs s ctr delta h.hT h.hnm).close H).congr e1 e2

/-- **Zero knowledge on the ideal tape** (`lean/docs/zk.md` H2, H5–H7): the ideal-tape prover's
output distribution is the simulator's, for every hash record and every satisfying witness. -/
theorem proveIdeal_close (h : ZKHyp T st w cs) :
    Close 0 (proveIdeal Hs T st w) (simulate st.params) := by
  have h1 : Close 0 (proveIdeal Hs T st w)
      (fun x : SimCoins st.params × Bytes (labelBytes st.params) => simulate st.params x.1) :=
    ((proveIdeal_theta_close Hs T st w cs h).map Prod.fst).congr (fun _ => by dsimp only)
      fun _ => by dsimp only
  have h2 : Close 0 (fun x : SimCoins st.params × Bytes (labelBytes st.params) =>
      simulate st.params x.1) (simulate st.params) := by
    intro D
    rw [pr_prod_fst (β := Bytes (labelBytes st.params)) (fun c => D (simulate st.params c))]
    simp
  exact (h1.trans h2).mono (by norm_num)

/-- **A guess of `Θ` from the proof is right with probability `2^{−8·|Θ|}`** (`2⁻¹²⁸` with
dedicated label rows): for any function `Q` of the ideal-tape prover's output, such as the offset
of an `H₅` query at a sibling label (`LabelRows.query_hits_sibling_iff_labelRows`). -/
theorem prove_guess_theta (h : ZKHyp T st w cs)
    (Q : Except String ByteArray → Bytes (labelBytes st.params)) :
    pr (IdealTape st.params) (fun t => Q (proveIdeal Hs T st w t) = t.2.2.1) =
      1 / 2 ^ (8 * labelBytes st.params) := by
  classical
  have := proveIdeal_theta_close Hs T st w cs h (fun o => Q o.1 = o.2)
  rw [abs_nonpos_iff, sub_eq_zero] at this
  rw [show (fun t : IdealTape st.params => Q (proveIdeal Hs T st w t) = t.2.2.1) =
    (fun t => Q (proveIdeal Hs T st w t, t.2.2.1).1 = (proveIdeal Hs T st w t, t.2.2.1).2) from rfl,
    this, pr_prod]
  have hθ : ∀ c : SimCoins st.params,
      pr (Bytes (labelBytes st.params)) (fun θ => Q (simulate st.params c, θ).1 = (simulate st.params c, θ).2) =
        1 / 2 ^ (8 * labelBytes st.params) := by
    intro c
    rw [pr_def]
    have : (univ.filter fun θ : Bytes (labelBytes st.params) => Q (simulate st.params c) = θ) =
        {Q (simulate st.params c)} := by ext; simp [eq_comm]
    simp only at this ⊢
    rw [this, card_singleton, Prob.card_bytes]
    push_cast
    ring
  simp only [hθ, sum_const, card_univ, nsmul_eq_mul]
  field_simp

end Close

end VoleMole.ZK.Sim
