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

/-- A domain the chain does not read (`H₃`, `H₂³`): neither chain input reads it. -/
lemma cin2_congr_unread {k : Kind} (hu : Unread k) (h : Hs.AgreeOff k Hs') :
    cin2 Hs T st proof = cin2 Hs' T st proof := by
  simp only [cin2, vLeaves_congr st proof h hu.1 hu.2.1 hu.2.2.1]
  split
  · rfl
  · simp only [in2Of, in1Of_congr st proof h hu.1 hu.2.1 hu.2.2.2.1,
      h.mu1 hu.1 hu.2.1 st, h .h21 (Ne.symm hu.2.2.2.2.1), h .h4 (Ne.symm hu.2.2.1),
      h .h5 (Ne.symm hu.2.2.2.2.2.2.1), h.muDelayed hu.1 st, crtReconstruct, ivOf]

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

/-! ## Sizes -/

section Sizes

variable (Hs : Hashes) (T : CrtTables) (st : Statement) (proof : ByteArray)

lemma size_field_le (pf : Proof) {k : String} {off n : ℕ} (hk : pf.params.field? k = some (off, n)) :
    (pf.field k).size ≤ n := by
  rw [field_eq pf hk, ByteArray.size_extract]
  omega

lemma size_hb (h : Array VoleMole.Arith.GF128) (h4 : h.size = 4) :
    (h.foldl (fun acc x => acc ++ gfToBytes x) ByteArray.empty).size = 64 := by
  have e4 : h = #[h[0]!, h[1]!, h[2]!, h[3]!] := by
    apply Array.ext
    · simp [h4]
    · intro i h1 h2
      simp only [h4] at h1
      interval_cases i <;> simp [getElem!_pos, h4]
  rw [e4]
  show (ByteArray.empty ++ gfToBytes _ ++ gfToBytes _ ++ gfToBytes _ ++ gfToBytes _).size = 64
  simp only [ByteArray.size_append, size_gfToBytes]
  rfl

/-- **The size of the verifier's `H₂¹` input.** -/
lemma size_cin1_le (hwf : HashesWF Hs) :
    (cin1 Hs st proof).size ≤ 64 + 16 * st.params.correctionBytes +
      st.params.nMask * st.params.nMultBytes + 16 + st.binder1.size + 1 := by
  unfold cin1
  split
  · simp
  · rename_i leaves _
    have hmu : (st.mu1 Hs).size = 32 := by
      unfold Statement.mu1 mu
      split <;> exact hwf _ _
    have hc : (BAVC.check (Hs.hash .h1) leaves.coms).size = 32 := hwf _ _
    have h1 := size_field_le (pfOf st proof) (Params.field_corrections st.params)
    have h2 := size_field_le (pfOf st proof) (Params.field_cmult st.params)
    have h3 := size_field_le (pfOf st proof) (Params.field_ivPre st.params)
    simp only [in1Of, chal1Input, ByteArray.size_push, ByteArray.size_append, hmu, hc]
    simp only [Proof.corrections, Proof.cmult, Proof.ivPre] at *
    omega

/-- **The size of the verifier's `H₂²` input.** -/
lemma size_cin2_le (hwf : HashesWF Hs) (hd : st.delayed = false) :
    (cin2 Hs T st proof).size ≤ 264 + st.binder2.size + st.params.witnessBytes + 1 := by
  unfold cin2
  split
  · simp
  · rename_i leaves _
    have h1 := size_field_le (pfOf st proof) (Params.field_voleCheck st.params)
    have h2 := size_field_le (pfOf st proof) (Params.field_correction st.params)
    have hmd : ∀ c, (st.muDelayed Hs c).size = 0 := fun c => by simp [Statement.muDelayed, hd]
    simp only [in2Of, chal2Input, ByteArray.size_push, ByteArray.size_append, hwf .h21,
      Kind.outLen, size_hb _ (voleHashReceiver_size _ _ _ _ _ _), hmd]
    simp only [Proof.voleCheck, Proof.correction] at *
    omega

/-- The counter field has at most four bytes. -/
lemma size_ctr_le (pf : Proof) : pf.ctr.size ≤ 4 :=
  size_field_le pf (Params.field_ctr pf.params)

end Sizes

/-! ## A hit on a simulated proof's prefix -/

section HitChain

variable (Hs : Hashes) (T : CrtTables)

/-- The simulator's recomputed prefix of an output (`outPre`, for a record `Hs`). -/
def simPre (st : Statement) (o : Except String ByteArray) : ByteArray :=
  match o with
  | .ok b => vPre Hs T st b
  | .error _ => ByteArray.empty

/-- The simulator's `H₂²` input. -/
def sim2 (st : Statement) (o : Except String ByteArray) : ByteArray :=
  match o with
  | .ok b => cin2 Hs T st b
  | .error _ => ByteArray.empty

/-- The simulator's `H₂¹` input. -/
def sim1 (st : Statement) (o : Except String ByteArray) : ByteArray :=
  match o with
  | .ok b => cin1 Hs st b
  | .error _ => ByteArray.empty

/-- **The chain of a hit.** If the verifier's grinding point of a proof `pf` for `stf` is the
grinding point of a `preLen`-byte block `blk pre` of a simulator's prefix `pre = simPre sts o`
(both non-delayed), then the forgery's reconstruction succeeds, and at the first level where the
inputs differ the outputs agree:

* `H₂²`: `cin2 ≠ sim2` and `H₂²(cin2) = (blk pre)[0, 56)`, or
* `H₂¹`: `cin1 ≠ sim1` and `H₂¹(cin1) = H₂¹(sim1)`, or
* `H₂⁰`: `muIn stf ≠ muIn sts` and `H₂⁰(muIn stf) = H₂⁰(muIn sts)`, or
* the simulation produced a proof and the two statements have the same `H₂⁰` input. -/
theorem chain_hit (hwf : HashesWF Hs) {p : Params} (stf sts : Statement) (pf : ByteArray)
    (o : Except String ByteArray) (hdf : stf.delayed = false) (hds : sts.delayed = false)
    (k : K2 p) (hk : enc2 p k = (vPre Hs T stf pf ++ (pfOf stf pf).ctr).push 11)
    (hkp : k.1 = blk (preLen p) (simPre Hs T sts o)) :
    (vLeaves Hs stf pf).isSome ∧
    ((cin2 Hs T stf pf ≠ sim2 Hs T sts o ∧
        Hs.hash .h22 (cin2 Hs T stf pf) = (ba (blk (preLen p) (simPre Hs T sts o))).extract 0 56) ∨
      (cin1 Hs stf pf ≠ sim1 Hs sts o ∧
        Hs.hash .h21 (cin1 Hs stf pf) = Hs.hash .h21 (sim1 Hs sts o)) ∨
      (muIn stf ≠ muIn sts ∧ Hs.hash .mu (muIn stf) = Hs.hash .mu (muIn sts)) ∨
      ((∃ b, o = .ok b) ∧ muIn stf = muIn sts)) := by
  have hpl : 56 ≤ preLen p := by unfold preLen; omega
  -- the grinding point: `vPre ‖ ctr = blk pre ‖ c`
  have he : vPre Hs T stf pf ++ (pfOf stf pf).ctr =
      ba k.1 ++ AES.pushLE32 ByteArray.empty k.2.val.toUInt32 := by
    have := hk.symm
    simp only [enc2, grindInput] at this
    rw [← pushLE32_eq]
    exact push_injective 11 this
  have hsz := congrArg ByteArray.size he
  have hctr := size_ctr_le (pfOf stf pf)
  simp only [ByteArray.size_append, size_ba, size_pushLE32, ByteArray.size_empty] at hsz
  rcases hv : vLeaves Hs stf pf with _ | leaves
  · rw [vPre_none Hs T stf pf hv] at hsz
    have h0 : ByteArray.empty.size = 0 := rfl
    omega
  refine ⟨rfl, ?_⟩
  -- the first 56 bytes: `chal2`
  have hc2 : Hs.hash .h22 (cin2 Hs T stf pf) = (ba (blk (preLen p) (simPre Hs T sts o))).extract 0 56 := by
    have e : (vPre Hs T stf pf ++ (pfOf stf pf).ctr).extract 0 56 =
        (ba k.1 ++ AES.pushLE32 ByteArray.empty k.2.val.toUInt32).extract 0 56 := by rw [he]
    rw [vPre_some Hs T stf pf hv, ByteArray.append_assoc,
      ByteArray.extract_append_eq_left (show (Hs.hash .h22 _).size = 56 from hwf .h22 _).symm] at e
    rw [e, ← hkp, ROM.extract_append_of_le (by rw [size_ba]; exact hpl)]
  by_cases h2 : cin2 Hs T stf pf = sim2 Hs T sts o
  swap
  · exact Or.inl ⟨h2, hc2⟩
  right
  -- the simulator's reconstruction succeeded
  have hne := cin2_ne_empty Hs T stf pf hv
  rcases o with e | b
  · exact absurd h2 hne
  simp only [sim2, sim1] at h2 ⊢
  have hvs : (vLeaves Hs sts b).isSome := (cin2_ne_empty_iff Hs T sts b).1 (h2 ▸ hne)
  obtain ⟨ls, hls⟩ := Option.isSome_iff_exists.1 hvs
  -- `chal1`
  obtain ⟨r, er⟩ := cin2_some Hs T stf pf hv
  obtain ⟨r', er'⟩ := cin2_some Hs T sts b hls
  have hc1 : Hs.hash .h21 (cin1 Hs stf pf) = Hs.hash .h21 (cin1 Hs sts b) := by
    have e := congrArg (fun b : ByteArray => b.extract 0 136) h2
    simp only [er, er'] at e
    have h136 : ∀ x, (Hs.hash .h21 x).size = 136 := fun x => hwf .h21 x
    rwa [extract_zero_append_push _ _ _ (h136 _), extract_zero_append_push _ _ _ (h136 _)] at e
  by_cases h1 : cin1 Hs stf pf = cin1 Hs sts b
  swap
  · exact Or.inl ⟨h1, hc1⟩
  right
  -- `mu₁`
  obtain ⟨u, eu⟩ := cin1_some Hs stf pf hv
  obtain ⟨u', eu'⟩ := cin1_some Hs sts b hls
  have hm : Hs.hash .mu (muIn stf) = Hs.hash .mu (muIn sts) := by
    have e := congrArg (fun b : ByteArray => b.extract 0 32) h1
    simp only [eu, eu'] at e
    have h32 : ∀ st : Statement, (st.mu1 Hs).size = 32 := fun st => by
      unfold Statement.mu1 mu
      split <;> exact hwf _ _
    rw [extract_zero_append_push _ _ _ (h32 _), extract_zero_append_push _ _ _ (h32 _),
      mu1_eq Hs stf hdf, mu1_eq Hs sts hds] at e
    exact e
  by_cases hmu : muIn stf = muIn sts
  · exact Or.inr ⟨⟨b, rfl⟩, hmu⟩
  · exact Or.inl ⟨hmu, hm⟩

end HitChain

end VoleMole.Theft.Chain
