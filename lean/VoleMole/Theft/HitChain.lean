import VoleMole.ZK.VerifyPre
import VoleMole.ROM.StmtBind

/-!
# The chain of the verifier's grinding prefix: `H₂⁰ → H₂¹ → H₂² → chal2`

The programming step of the theft theorems (`Theft/SimExtract.lean`) leaves the term `ε_hit`: a
fresh forgery whose verifier's `H₂³` point (`vPoint`) is a point a simulator programmed. The
programmed points are the grinding points of the prefix `chal2 ‖ qs_check ‖ ã` the simulator
recomputes from its proof (`outPre`, `progRO_moved`), and the verifier's point is the grinding
point of the forgery's prefix (`vPre`). So a hit means that the forgery's `chal2` equals a
simulated proof's. Here the chain behind `chal2` is made explicit:

* `vLeaves`: the BAVC reconstruction of the verifier (none: the prefix is empty, `vPre_none`).
* `cin1`, `cin2`: the verifier's `H₂¹` and `H₂²` inputs (empty when the reconstruction fails).
* **Structure.** `vPre = H₂²(cin2) ‖ …` (`vPre_some`), `cin2 = (H₂¹(cin1) ‖ …) ‖ 10`
  (`cin2_some`), `cin1 = (mu₁ ‖ …) ‖ 9` (`cin1_some`), and for a non-delayed statement
  `mu₁ = H₂⁰(muIn st)`.
* **Each level is read at one point.** Two records that agree off `H₂²` and at `cin2` give the
  same prefix, and `cin2` does not read `H₂²` (`vPre_congr22`, `cin2_congr22`); the same for `H₂¹`
  at `cin1` (`vPre_congr21`, `cin2_congr21`, `cin1_congr21`) and for `H₂⁰` at `muIn st`
  (`vPre_congrMu`, …), for non-delayed statements.

These are the "chain structure" facts `ε_hit` needs (`Theft/Hit.lean`).
-/

namespace VoleMole.Theft.Chain

-- The statements hold for any CTR PRG (`HasPrg`, `Verifier/Prg.lean`), the ideal cipher included.
variable [VoleMole.Verifier.HasPrg]
set_option linter.unusedSectionVars false

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim VoleMole.ZK VoleMole.ROM
open VoleMole.ROM.IC (muIn)

/-! ## The verifier's chain inputs -/

section Defs

variable (Hs : Hashes) (T : CrtTables) (st : Statement) (proof : ByteArray)

/-- The proof as the verifier parses it. -/
def pfOf : Proof := { params := st.params, bytes := proof }

/-- **The verifier's BAVC reconstruction.** -/
def vLeaves : Option BAVC.Leaves :=
  BAVC.reconstruct (ivOf Hs (pfOf st proof) (st.mu1 Hs)) (pfOf st proof).opening
    (pfOf st proof).delta

/-- The `H₂¹` input from the reconstructed leaves. -/
def in1Of (leaves : BAVC.Leaves) : ByteArray :=
  chal1Input (pfOf st proof) (st.mu1 Hs) (BAVC.check (Hs.hash .h1) leaves.coms) st.binder1

/-- The `H₂²` input from the reconstructed leaves. -/
def in2Of (leaves : BAVC.Leaves) : ByteArray :=
  let pf := pfOf st proof
  let c1 := Hs.hash .h21 (in1Of Hs st proof leaves)
  let crt := crtReconstruct Hs pf T (ivOf Hs pf (st.mu1 Hs))
    (convertToVole pf (ivOf Hs pf (st.mu1 Hs)) leaves)
  let deltaL := crt.deltaLifted.toGF
  let hV := voleHashReceiver st.params c1 crt.rows crt.qMask deltaL pf.voleCheck
  chal2Input pf c1 hV (st.muDelayed Hs c1) st.binder2

/-- The prefix after `chal2`, from the reconstructed leaves and `chal2`. -/
def restOf (leaves : BAVC.Leaves) (c2 : ByteArray) : ByteArray :=
  let pf := pfOf st proof
  let c1 := Hs.hash .h21 (in1Of Hs st proof leaves)
  let crt := crtReconstruct Hs pf T (ivOf Hs pf (st.mu1 Hs))
    (convertToVole pf (ivOf Hs pf (st.mu1 Hs)) leaves)
  let deltaL := crt.deltaLifted.toGF
  let cs := constraintKeys st.params (correctedKeys pf crt.rows deltaL) deltaL
    (st.values c1 (st.combBytes Hs c2))
  gfToBytes (qsCheck pf c2 cs crt.qMask deltaL) ++ pf.qsProof

/-- **The verifier's `H₂¹` input** (empty if the reconstruction fails). -/
def cin1 : ByteArray :=
  match vLeaves Hs st proof with
  | none => ByteArray.empty
  | some leaves => in1Of Hs st proof leaves

/-- **The verifier's `H₂²` input** (empty if the reconstruction fails). -/
def cin2 : ByteArray :=
  match vLeaves Hs st proof with
  | none => ByteArray.empty
  | some leaves => in2Of Hs T st proof leaves

end Defs

/-! ## Structure -/

section Structure

variable (Hs : Hashes) (T : CrtTables) (st : Statement) (proof : ByteArray)

lemma vPreOf_eq (leaves : BAVC.Leaves) :
    vPreOf Hs T st (pfOf st proof) leaves =
      Hs.hash .h22 (in2Of Hs T st proof leaves) ++
        restOf Hs T st proof leaves (Hs.hash .h22 (in2Of Hs T st proof leaves)) := by
  simp only [vPreOf, restOf, in2Of, in1Of, chal1, chal2, ByteArray.append_assoc]

lemma vPre_none (h : vLeaves Hs st proof = none) : vPre Hs T st proof = ByteArray.empty := by
  simp only [vLeaves] at h
  simp only [vPre, vPreP]
  rw [show ({ params := st.params, bytes := proof } : Proof) = pfOf st proof from rfl, h]

/-- **The prefix begins with `H₂²(cin2)`.** -/
lemma vPre_some {leaves : BAVC.Leaves} (h : vLeaves Hs st proof = some leaves) :
    vPre Hs T st proof = Hs.hash .h22 (cin2 Hs T st proof) ++
      restOf Hs T st proof leaves (Hs.hash .h22 (cin2 Hs T st proof)) := by
  simp only [vLeaves] at h
  have e : cin2 Hs T st proof = in2Of Hs T st proof leaves := by
    simp only [cin2, vLeaves, h]
  rw [e, ← vPreOf_eq]
  simp only [vPre, vPreP]
  rw [show ({ params := st.params, bytes := proof } : Proof) = pfOf st proof from rfl, h]

/-- **`cin2` begins with `H₂¹(cin1)`.** -/
lemma cin2_some {leaves : BAVC.Leaves} (h : vLeaves Hs st proof = some leaves) :
    ∃ r, cin2 Hs T st proof = (Hs.hash .h21 (cin1 Hs st proof) ++ r).push 10 := by
  simp only [cin2, cin1, h, in2Of, chal2Input, ByteArray.append_assoc]
  exact ⟨_, rfl⟩

/-- **`cin1` begins with `mu₁`.** -/
lemma cin1_some {leaves : BAVC.Leaves} (h : vLeaves Hs st proof = some leaves) :
    ∃ r, cin1 Hs st proof = (st.mu1 Hs ++ r).push 9 := by
  simp only [cin1, h, in1Of, chal1Input, ByteArray.append_assoc]
  exact ⟨_, rfl⟩

lemma cin1_ne_empty {leaves : BAVC.Leaves} (h : vLeaves Hs st proof = some leaves) :
    cin1 Hs st proof ≠ ByteArray.empty := by
  obtain ⟨r, e⟩ := cin1_some Hs st proof h
  rw [e]
  intro h'
  have := congrArg ByteArray.size h'
  simp at this

lemma cin2_ne_empty {leaves : BAVC.Leaves} (h : vLeaves Hs st proof = some leaves) :
    cin2 Hs T st proof ≠ ByteArray.empty := by
  obtain ⟨r, e⟩ := cin2_some Hs T st proof h
  rw [e]
  intro h'
  have := congrArg ByteArray.size h'
  simp at this

/-- For a non-delayed statement `mu₁` is `H₂⁰` at `muIn st`. -/
lemma mu1_eq (hd : st.delayed = false) : st.mu1 Hs = Hs.hash .mu (muIn st) := by
  simp [Statement.mu1, hd, mu, muIn]

/-- `vLeaves` is `none` or `some`, with `cin2` nonempty in the second case. -/
lemma cin2_ne_empty_iff : cin2 Hs T st proof ≠ ByteArray.empty ↔ (vLeaves Hs st proof).isSome := by
  rcases h : vLeaves Hs st proof with _ | leaves
  · simp [cin2, h]
  · simp only [Option.isSome_some, iff_true]
    exact cin2_ne_empty Hs T st proof h

end Structure

/-! ## Each level is read at one point -/

section Congr

variable {Hs Hs' : Hashes} (T : CrtTables) (st : Statement) (proof : ByteArray)

/-- Records that agree off `H₂²`: the reconstruction and both chain inputs agree. -/
lemma vLeaves_congr {k : Kind} (h : Hs.AgreeOff k Hs') (h1 : k ≠ .mu) (h2 : k ≠ .muDelayed)
    (h4 : k ≠ .h4) : vLeaves Hs st proof = vLeaves Hs' st proof := by
  simp only [vLeaves, ivOf, h.mu1 h1 h2 st, h .h4 (Ne.symm h4)]

lemma in1Of_congr {k : Kind} (h : Hs.AgreeOff k Hs') (h1 : k ≠ .mu) (h2 : k ≠ .muDelayed)
    (h3 : k ≠ .h1) (leaves : BAVC.Leaves) :
    in1Of Hs st proof leaves = in1Of Hs' st proof leaves := by
  simp only [in1Of, h.mu1 h1 h2 st, h .h1 (Ne.symm h3)]

lemma cin1_congr {k : Kind} (h : Hs.AgreeOff k Hs') (h1 : k ≠ .mu) (h2 : k ≠ .muDelayed)
    (h3 : k ≠ .h1) (h4 : k ≠ .h4) : cin1 Hs st proof = cin1 Hs' st proof := by
  simp only [cin1, vLeaves_congr st proof h h1 h2 h4]
  split <;> simp only [in1Of_congr st proof h h1 h2 h3]

/-- **`H₂²`**: `cin2` does not read it. -/
lemma cin2_congr22 (h : Hs.AgreeOff .h22 Hs') : cin2 Hs T st proof = cin2 Hs' T st proof := by
  simp only [cin2, vLeaves_congr st proof h (by decide) (by decide) (by decide)]
  split
  · rfl
  · simp only [in2Of, in1Of_congr st proof h (by decide) (by decide) (by decide),
      h.mu1 (by decide) (by decide) st, h .h21 (by decide), h .h4 (by decide), h .h5 (by decide),
      h.muDelayed (by decide) st, crtReconstruct, ivOf]

/-- **`H₂²` is read at `cin2` only**: records that agree off `H₂²` and at `cin2` give the same
prefix. -/
lemma vPre_congr22 (h : Hs.AgreeOff .h22 Hs')
    (hp : Hs.hash .h22 (cin2 Hs T st proof) = Hs'.hash .h22 (cin2 Hs T st proof)) :
    vPre Hs T st proof = vPre Hs' T st proof := by
  have hl := vLeaves_congr st proof h (by decide) (by decide) (by decide)
  rcases hv : vLeaves Hs st proof with _ | leaves
  · rw [vPre_none Hs T st proof hv, vPre_none Hs' T st proof (hl ▸ hv)]
  · have hv' : vLeaves Hs' st proof = some leaves := hl ▸ hv
    have hr : ∀ c, restOf Hs T st proof leaves c = restOf Hs' T st proof leaves c := fun c => by
      simp only [restOf, in1Of_congr st proof h (by decide) (by decide) (by decide),
        h.mu1 (by decide) (by decide) st, h .h21 (by decide), h .h4 (by decide), h .h5 (by decide),
        h.combBytes (fun _ => nofun) st, crtReconstruct, ivOf]
    rw [vPre_some Hs T st proof hv, vPre_some Hs' T st proof hv', ← cin2_congr22 T st proof h, ← hp,
      hr]

/-- **`H₂¹`**: `cin1` does not read it. -/
lemma cin1_congr21 (h : Hs.AgreeOff .h21 Hs') : cin1 Hs st proof = cin1 Hs' st proof :=
  cin1_congr st proof h (by decide) (by decide) (by decide) (by decide)

/-- **`H₂¹` is read at `cin1` only**: `cin2`. -/
lemma cin2_congr21 (h : Hs.AgreeOff .h21 Hs')
    (hp : Hs.hash .h21 (cin1 Hs st proof) = Hs'.hash .h21 (cin1 Hs st proof)) :
    cin2 Hs T st proof = cin2 Hs' T st proof := by
  have hl := vLeaves_congr st proof h (by decide) (by decide) (by decide)
  rcases hv : vLeaves Hs st proof with _ | leaves
  · simp only [cin2, hv, ← hl]
  · have hv' : vLeaves Hs' st proof = some leaves := hl ▸ hv
    have hp' : Hs.hash .h21 (in1Of Hs st proof leaves) = Hs'.hash .h21 (in1Of Hs' st proof leaves) := by
      rw [← in1Of_congr st proof h (by decide) (by decide) (by decide)]
      simpa only [cin1, hv] using hp
    simp only [cin2, hv, hv', in2Of]
    rw [hp']
    simp only [h.mu1 (by decide) (by decide) st, h .h4 (by decide), h .h5 (by decide),
      h.muDelayed (by decide) st, crtReconstruct, ivOf]

/-- **`H₂¹` is read at `cin1` only**: the prefix. -/
lemma vPre_congr21 (h : Hs.AgreeOff .h21 Hs')
    (hp : Hs.hash .h21 (cin1 Hs st proof) = Hs'.hash .h21 (cin1 Hs st proof)) :
    vPre Hs T st proof = vPre Hs' T st proof := by
  have hl := vLeaves_congr st proof h (by decide) (by decide) (by decide)
  rcases hv : vLeaves Hs st proof with _ | leaves
  · rw [vPre_none Hs T st proof hv, vPre_none Hs' T st proof (hl ▸ hv)]
  · have hv' : vLeaves Hs' st proof = some leaves := hl ▸ hv
    have hp' : Hs.hash .h21 (in1Of Hs st proof leaves) = Hs'.hash .h21 (in1Of Hs' st proof leaves) := by
      rw [← in1Of_congr st proof h (by decide) (by decide) (by decide)]
      simpa only [cin1, hv] using hp
    have hr : ∀ c, restOf Hs T st proof leaves c = restOf Hs' T st proof leaves c := fun c => by
      simp only [restOf]
      rw [hp']
      simp only [h.mu1 (by decide) (by decide) st, h .h4 (by decide), h .h5 (by decide),
        h.combBytes (fun _ => nofun) st, crtReconstruct, ivOf]
    rw [vPre_some Hs T st proof hv, vPre_some Hs' T st proof hv', ← cin2_congr21 T st proof h hp,
      h .h22 (by decide), hr]

variable {st} (hd : st.delayed = false)
include hd

/-- **`H₂⁰`, non-delayed**: `mu₁` is read at `muIn st` only. -/
lemma mu1_congrMu (hp : Hs.hash .mu (muIn st) = Hs'.hash .mu (muIn st)) : st.mu1 Hs = st.mu1 Hs' := by
  rw [mu1_eq Hs st hd, mu1_eq Hs' st hd, hp]

lemma muDelayed_congrMu : st.muDelayed Hs = st.muDelayed Hs' := by
  funext c
  simp [Statement.muDelayed, hd]

lemma vLeaves_congrMu (h : Hs.AgreeOff .mu Hs')
    (hp : Hs.hash .mu (muIn st) = Hs'.hash .mu (muIn st)) :
    vLeaves Hs st proof = vLeaves Hs' st proof := by
  simp only [vLeaves, ivOf, mu1_congrMu hd hp, h .h4 (by decide)]

lemma in1Of_congrMu (h : Hs.AgreeOff .mu Hs')
    (hp : Hs.hash .mu (muIn st) = Hs'.hash .mu (muIn st)) (leaves : BAVC.Leaves) :
    in1Of Hs st proof leaves = in1Of Hs' st proof leaves := by
  simp only [in1Of, mu1_congrMu hd hp, h .h1 (by decide)]

lemma cin1_congrMu (h : Hs.AgreeOff .mu Hs')
    (hp : Hs.hash .mu (muIn st) = Hs'.hash .mu (muIn st)) : cin1 Hs st proof = cin1 Hs' st proof := by
  simp only [cin1, vLeaves_congrMu proof hd h hp]
  split <;> simp only [in1Of_congrMu proof hd h hp]

lemma cin2_congrMu (h : Hs.AgreeOff .mu Hs')
    (hp : Hs.hash .mu (muIn st) = Hs'.hash .mu (muIn st)) :
    cin2 Hs T st proof = cin2 Hs' T st proof := by
  simp only [cin2, vLeaves_congrMu proof hd h hp]
  split
  · rfl
  · simp only [in2Of, in1Of_congrMu proof hd h hp, mu1_congrMu hd hp, h .h21 (by decide),
      h .h4 (by decide), h .h5 (by decide), muDelayed_congrMu hd (Hs := Hs) (Hs' := Hs'),
      crtReconstruct, ivOf]

/-- **`H₂⁰` is read at `muIn st` only**: the prefix. -/
lemma vPre_congrMu (h : Hs.AgreeOff .mu Hs')
    (hp : Hs.hash .mu (muIn st) = Hs'.hash .mu (muIn st)) :
    vPre Hs T st proof = vPre Hs' T st proof := by
  have hl := vLeaves_congrMu proof hd h hp
  rcases hv : vLeaves Hs st proof with _ | leaves
  · rw [vPre_none Hs T st proof hv, vPre_none Hs' T st proof (hl ▸ hv)]
  · have hv' : vLeaves Hs' st proof = some leaves := hl ▸ hv
    have hr : ∀ c, restOf Hs T st proof leaves c = restOf Hs' T st proof leaves c := fun c => by
      simp only [restOf, in1Of_congrMu proof hd h hp, mu1_congrMu hd hp, h .h21 (by decide),
        h .h4 (by decide), h .h5 (by decide), h.combBytes (fun _ => nofun) st, crtReconstruct, ivOf]
    rw [vPre_some Hs T st proof hv, vPre_some Hs' T st proof hv', ← cin2_congrMu T proof hd h hp,
      h .h22 (by decide), hr]

end Congr

end VoleMole.Theft.Chain
