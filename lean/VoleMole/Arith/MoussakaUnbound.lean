import VoleMole.Arith.Moussaka

/-!
# Unbound Moussaka issue and redeem (`src/moussaka/unbound_issue.hpp`, `unbound_redeem.hpp`)

Executable models of `UnboundIssueRelation::constraints` and `UnboundRedeemRelation::constraints`
(PR #63), with completeness and soundness against the relations that
`lean/docs/security/moussaka-unbound.md` §2 uses:

* **unbound issue**: `t = UCom(k, ctx_iss, r)`, with
  `UCom(x) = keccak_p800(encode_unbound_com_state(x))[0..45)` (`moussaka.cpp:326-332`);
* **unbound redeem**: a one-hot selector `b = e_{u₀}` with `u₀ < |anchors|`,
  `P_{anchors[u₀]}(σ) = UCom(k, ctx_iss, r)` in all 45 components, and
  `nf = Derive(k, ctx_red) = keccak_p800(encode_derive_state(k, ctx_red))[0..24)`
  (`moussaka.cpp:334-340`).

## Model

* `UCom` input (`commit.hpp:62-81`, `encodeUnboundComState`):
  `"mous" ‖ 0x01 ‖ "c0" ‖ r ‖ 0⁹ ‖ ctx_iss ‖ k ‖ 0³⁶` (offsets 0, 7, 32, 48, 64).
* `Derive` input (`commit.hpp:83-98`, `encodeDeriveState`):
  `"mous" ‖ 0x01 ‖ "d0" ‖ k ‖ 0⁹ ‖ ctx_red ‖ 0⁵²` (offsets 0, 7, 32, 48).
* Issue witness (`unbound_issue.hpp`): `r = [0,16)`, `k = [16,32)`, states at byte 32 (`232`
  bytes). Constraints: 1856 bit constraints, `qs_keccak(…, 32, 360)`'s 1600, and `out[i] + t_i`
  for `i < 360` (the bound issue's `issueOutput`): 3816.
* Redeem witness (`unbound_redeem.hpp`): `r = [0,16)`, `k = [16,32)`, `s = [32,151)`, the `UCom`
  states at 151, the `Derive` states at 351, selector bit `b[u]` at witness bit `8·551 + u`.
  Constraints, in order: 4408 bit constraints; the selector constraints (`MAX_ANCHORS = 64`); the
  1600 of `qs_keccak(UCom, 151)` (all 800 output bits); the 1600 of `qs_keccak(Derive, 351, 192)`;
  `out_D[i] + nf_i` for `i < 192`; the combined output constraint `lout + lq` on `out_C`: 7929.
* `l : Fin 45 → F` is `Combination(chal2, UNBOUND_MOUSSAKA_REDEEM_COMBINE_DST)`, an argument.

## Main results

* Domain separation of the Keccak inputs: `encodeUnboundComState_ne_encodeComState`,
  `encodeDeriveState_ne_encodeUnboundComState`, `encodeDeriveState_ne_encodeComState` (the three
  input sets are disjoint); `encodeUnboundComState_inj`, `encodeDeriveState_inj` (each encoding is
  injective in its variable fields).
* Wiring: `inputState_uIssue`, `inputState_uRedeemCom`, `inputState_uRedeemDerive`.
* Issue: `uIssueSystem_length` (3816), `uIssue_complete`, `uIssue_sound`.
* Redeem: `uRedeemSystem_length` (7929), `uRedeem_complete`, `uRedeem_sound`, and the end-to-end
  `uRedeem_sound_card`: for committed values fixed before `l`, either they encode a witness of the
  unbound redeem relation, or at most a `1/|F|` fraction of the `l` make every constraint hold.
* Executable values with sharing: `uIssueValues_eq`, `uRedeemValues_eq`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace VoleMole.Arith.MoussakaUnbound

open VoleMole.Arith UOV Keccak _root_.VoleMole.Arith.Moussaka

/-! ## The two Keccak inputs -/

/-- `UNBOUND_MOUSSAKA_COM_DST = make_dst("mous", UNBOUND_VERSION = 1, 'c', '0')`. -/
def ucomDst : List UInt8 := [0x6d, 0x6f, 0x75, 0x73, 0x01, 0x63, 0x30]

/-- `UNBOUND_MOUSSAKA_DERIVE_DST = make_dst("mous", UNBOUND_VERSION = 1, 'd', '0')`. -/
def deriveDst : List UInt8 := [0x6d, 0x6f, 0x75, 0x73, 0x01, 0x64, 0x30]

/-- `encode_unbound_com_state(nf_key, ctx_iss, r)` (`commit.hpp:73-81`), with
`UNBOUND_COM_OFF_R = 7`, `UNBOUND_COM_OFF_CTX_ISS = 32`, `UNBOUND_COM_OFF_NF_KEY = 48`. -/
def encodeUnboundComState (k ctxIss r : ℕ → UInt8) : State :=
  Vector.ofFn fun i =>
    if i.val < 7 then ucomDst.getD i.val 0
    else if i.val < 23 then r (i.val - 7)
    else if i.val < 32 then 0
    else if i.val < 48 then ctxIss (i.val - 32)
    else if i.val < 64 then k (i.val - 48)
    else 0

/-- `encode_derive_state(nf_key, ctx_red)` (`commit.hpp:92-98`), with `DERIVE_OFF_NF_KEY = 7`,
`DERIVE_OFF_CTX_RED = 32`. -/
def encodeDeriveState (k ctxRed : ℕ → UInt8) : State :=
  Vector.ofFn fun i =>
    if i.val < 7 then deriveDst.getD i.val 0
    else if i.val < 23 then k (i.val - 7)
    else if i.val < 32 then 0
    else if i.val < 48 then ctxRed (i.val - 32)
    else 0

/-- `UCom(nf_key, ctx_iss, r)` (`unbound_commit`, `moussaka.cpp:326-332`). -/
def ucom (k ctxIss r : ℕ → UInt8) (j : Fin M) : UInt8 :=
  (keccakP800 (encodeUnboundComState k ctxIss r))[j.val]

/-- `NF_BYTES`. -/
abbrev NF : ℕ := 24

/-- `Derive(nf_key, ctx_red)` (`derive`, `moussaka.cpp:334-340`). -/
def derive (k ctxRed : ℕ → UInt8) (j : Fin NF) : UInt8 :=
  (keccakP800 (encodeDeriveState k ctxRed))[j.val]

/-! ### Domain separation and injectivity -/

/-- The bound and unbound commitment inputs differ in byte 4 (the version byte). -/
theorem encodeUnboundComState_ne_encodeComState (k ctxIss r nf ctxIss' ctxRed r' : ℕ → UInt8) :
    encodeUnboundComState k ctxIss r ≠ encodeComState nf ctxIss' ctxRed r' := fun h => by
  have := congrArg (fun s : State => s[4]) h
  simp [encodeUnboundComState, encodeComState, ucomDst, comDst] at this

/-- `Derive`'s input differs from `UCom`'s in byte 5 (purpose `'d'` against `'c'`). -/
theorem encodeDeriveState_ne_encodeUnboundComState (k ctxRed k' ctxIss r : ℕ → UInt8) :
    encodeDeriveState k ctxRed ≠ encodeUnboundComState k' ctxIss r := fun h => by
  have := congrArg (fun s : State => s[5]) h
  simp [encodeUnboundComState, encodeDeriveState, ucomDst, deriveDst] at this

/-- `Derive`'s input differs from the bound commitment's in byte 4. -/
theorem encodeDeriveState_ne_encodeComState (k ctxRed nf ctxIss ctxRed' r : ℕ → UInt8) :
    encodeDeriveState k ctxRed ≠ encodeComState nf ctxIss ctxRed' r := fun h => by
  have := congrArg (fun s : State => s[4]) h
  simp [encodeDeriveState, encodeComState, deriveDst, comDst] at this

/-- `encode_unbound_com_state` is injective in `(r, ctx_iss, nf_key)` on their 16 bytes. -/
theorem encodeUnboundComState_inj {k ctxIss r k' ctxIss' r' : ℕ → UInt8}
    (h : encodeUnboundComState k ctxIss r = encodeUnboundComState k' ctxIss' r') :
    (∀ i < 16, r i = r' i) ∧ (∀ i < 16, ctxIss i = ctxIss' i) ∧ (∀ i < 16, k i = k' i) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · have := congrArg (fun s : State => s[7 + i]'(by omega)) h
    simpa [encodeUnboundComState, show ¬ 7 + i < 7 by omega, show 7 + i < 23 by omega] using this
  · have := congrArg (fun s : State => s[32 + i]'(by omega)) h
    simpa [encodeUnboundComState, show ¬ 32 + i < 7 by omega, show ¬ 32 + i < 23 by omega,
      show ¬ 32 + i < 32 by omega, show 32 + i < 48 by omega] using this
  · have := congrArg (fun s : State => s[48 + i]'(by omega)) h
    simpa [encodeUnboundComState, show ¬ 48 + i < 7 by omega, show ¬ 48 + i < 23 by omega,
      show ¬ 48 + i < 32 by omega, show ¬ 48 + i < 48 by omega, show 48 + i < 64 by omega] using this

/-- `encode_derive_state` is injective in `(nf_key, ctx_red)` on their 16 bytes. -/
theorem encodeDeriveState_inj {k ctxRed k' ctxRed' : ℕ → UInt8}
    (h : encodeDeriveState k ctxRed = encodeDeriveState k' ctxRed') :
    (∀ i < 16, k i = k' i) ∧ (∀ i < 16, ctxRed i = ctxRed' i) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have := congrArg (fun s : State => s[7 + i]'(by omega)) h
    simpa [encodeDeriveState, show ¬ 7 + i < 7 by omega, show 7 + i < 23 by omega] using this
  · have := congrArg (fun s : State => s[32 + i]'(by omega)) h
    simpa [encodeDeriveState, show ¬ 32 + i < 7 by omega, show ¬ 32 + i < 23 by omega,
      show ¬ 32 + i < 32 by omega, show 32 + i < 48 by omega] using this

/-! ## Issue (`src/moussaka/unbound_issue.hpp`) -/

section Issue

/-- `UNBOUND_ISSUE_WIT_OFF_R`, `_NF_KEY`, `_STATES`. -/
def uIssueOffR : ℕ := 0
def uIssueOffK : ℕ := 16
def uIssueOffStates : ℕ := 32

/-- `UNBOUND_ISSUE_WITNESS_BITS = 8 · 232`. -/
def uIssueWitnessBits : ℕ := 8 * 232

/-- `UNBOUND_COM_TO_WIT`: `r` and `nf_key` are secret. -/
def uIssueMap : Fin 100 → Option ℕ := fun i =>
  if 7 ≤ i.val ∧ i.val < 23 then some (uIssueOffR + (i.val - 7))
  else if 48 ≤ i.val ∧ i.val < 64 then some (uIssueOffK + (i.val - 48))
  else none

/-- `encode_unbound_com_state({}, x.ctx_iss, {})`. -/
def uIssuePub (ctxIss : ℕ → UInt8) : State :=
  encodeUnboundComState (fun _ => 0) ctxIss (fun _ => 0)

/-- Decoded witness fields. -/
def uIssueR (w : ℕ → Bool) : ℕ → UInt8 := fun i => witByte w (uIssueOffR + i)
def uIssueK (w : ℕ → Bool) : ℕ → UInt8 := fun i => witByte w (uIssueOffK + i)

/-- **Input wiring**: the Keccak input built by `qs_input(encode_unbound_com_state({}, ctx_iss,
{}), UNBOUND_COM_TO_WIT)` is `encode_unbound_com_state(nf_key, ctx_iss, r)` of the decoded
witness. -/
theorem inputState_uIssue (ctxIss : ℕ → UInt8) (w : ℕ → Bool) :
    inputState (uIssuePub ctxIss) uIssueMap w =
      encodeUnboundComState (uIssueK w) ctxIss (uIssueR w) := by
  apply Vector.ext
  intro i hi
  simp only [inputState, Vector.getElem_ofFn]
  unfold uIssueMap
  simp only [uIssuePub, encodeUnboundComState, Vector.getElem_ofFn, uIssueR, uIssueK, uIssueOffR,
    uIssueOffK]
  by_cases a1 : i < 7
  · simp [a1, show ¬ 7 ≤ i by omega, show ¬ 48 ≤ i by omega]
  by_cases a2 : i < 23
  · simp [a1, a2, show 7 ≤ i by omega]
  by_cases a3 : i < 48
  · simp [a1, a2, a3, show ¬ 48 ≤ i by omega]
  by_cases a4 : i < 64
  · simp [a1, a2, a3, a4, show 48 ≤ i by omega, show ¬ i < 32 by omega]
  · simp [a1, a2, a3, a4]

variable {F : Type*}

/-- `qs_keccak(qs_input(…), UNBOUND_ISSUE_WIT_OFF_STATES, 8M)`. -/
def uIssueKeccak [Zero F] [One F] (ctxIss : ℕ → UInt8) : System F × Vector (Expr F) 360 :=
  qsKeccak uIssueOffStates 360 (by norm_num) (qsInput (uIssuePub ctxIss) uIssueMap)

/-- `UnboundIssueRelation::constraints(qs, {t, ctx_iss}, chal2)`. -/
def uIssueSystem [Add F] [Mul F] [Zero F] [One F] (t : Fin M → UInt8) (ctxIss : ℕ → UInt8) :
    System F :=
  bitSystem uIssueWitnessBits ++ (uIssueKeccak ctxIss).1 ++ issueOutput t (uIssueKeccak ctxIss).2

theorem uIssueSystem_length [Add F] [Mul F] [Zero F] [One F] (t : Fin M → UInt8)
    (ctxIss : ℕ → UInt8) : (uIssueSystem (F := F) t ctxIss).length = 3816 := by
  simp [uIssueSystem, bitSystem, issueOutput, uIssueKeccak, qsKeccak_length, uIssueWitnessBits]

/-- The constraint values computed with sharing (`qsKeccakValues`). -/
def uIssueValues [Add F] [Mul F] [Zero F] [One F] (t : Fin M → UInt8) (ctxIss : ℕ → UInt8)
    (w : ℕ → F) : List F :=
  let kv := qsKeccakValues w uIssueOffStates 360 (by norm_num)
    ((qsInput (F := F) (uIssuePub ctxIss) uIssueMap).map (Expr.eval w))
  (bitSystem uIssueWitnessBits).values w ++ kv.1 ++
    (List.finRange 360).map fun i => kv.2[i] + bitF (tBit t i)

theorem uIssueValues_eq [Add F] [Mul F] [Zero F] [One F] (t : Fin M → UInt8)
    (ctxIss : ℕ → UInt8) (w : ℕ → F) :
    uIssueValues t ctxIss w = (uIssueSystem t ctxIss).values w := by
  obtain ⟨h1, h2⟩ := qsKeccak_values w uIssueOffStates 360 (by norm_num)
    (qsInput (F := F) (uIssuePub ctxIss) uIssueMap)
  unfold uIssueValues uIssueSystem uIssueKeccak
  dsimp only
  rw [System.values] at h1
  rw [System.values, System.values, List.map_append, List.map_append, h1, issueOutput,
    List.map_map]
  rw [List.append_cancel_left_eq]
  refine List.map_congr_left fun i _ => ?_
  have := congrArg (fun v => v[i]) h2
  simp only [Vector.getElem_map, Fin.getElem_fin] at this
  simp only [Function.comp, Expr.eval_add, Expr.eval_const, Fin.getElem_fin, this]

/-- The unbound issue relation: `t = UCom(nf_key, ctx_iss, r)`. -/
def uIssueRel (t : Fin M → UInt8) (ctxIss k r : ℕ → UInt8) : Prop :=
  t = ucom k ctxIss r

variable [Field F] [CharP F 2]

theorem uIssueMap_lt : ∀ i b, uIssueMap i = some b → b < uIssueWitnessBits / 8 := by
  intro i b h
  simp only [uIssueMap, uIssueOffR, uIssueOffK] at h
  split_ifs at h <;> simp only [Option.some.injEq] at h <;> simp only [uIssueWitnessBits] <;> omega

/-- **Completeness.** A bit vector with arbitrary `r`, `nf_key`, honest committed states and
`t = UCom(nf_key, ctx_iss, r)` satisfies every constraint. -/
theorem uIssue_complete (t : Fin M → UInt8) (ctxIss : ℕ → UInt8) (w : ℕ → Bool)
    (h5 : ∀ i < 800, w (8 * uIssueOffStates + i) =
      stateBit (keccakP800Rounds 0 5 (encodeUnboundComState (uIssueK w) ctxIss (uIssueR w))) i)
    (h9 : ∀ i < 800, w (8 * (uIssueOffStates + 100) + i) =
      stateBit (keccakP800Rounds 0 9 (encodeUnboundComState (uIssueK w) ctxIss (uIssueR w))) i)
    (hrel : uIssueRel t ctxIss (uIssueK w) (uIssueR w)) :
    (uIssueSystem t ctxIss).Holds (ofBits w : ℕ → F) := by
  rw [← inputState_uIssue] at h5 h9
  have hK := qsKeccak_complete (F := F) (uIssuePub ctxIss) uIssueMap w uIssueOffStates 360
    (by norm_num) h5 h9
  rw [uIssueSystem, System.holds_append, System.holds_append]
  refine ⟨⟨bitSystem_holds _ w, hK⟩, ?_⟩
  intro e he
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
  have hi := i.isLt
  rw [Expr.eval_add, Expr.eval_const, uIssueKeccak, Fin.getElem_fin,
    qsKeccak_sound (uIssuePub ctxIss) uIssueMap w _ 360 _ hK i.val hi]
  have hb : stateBit (keccakP800 (inputState (uIssuePub ctxIss) uIssueMap w)) i.val = tBit t i := by
    rw [stateBit_eq _ _ (by omega), tBit, hrel, ucom, inputState_uIssue]
  rw [hb]; exact CharTwo.add_self_eq_zero _

/-- **Soundness.** If the constraints hold at any committed values `w ∈ F^ℓ`, all `8·232` witness
bits are bits, and their decoding satisfies `t = UCom(nf_key, ctx_iss, r)`. -/
theorem uIssue_sound [DecidableEq F] (t : Fin M → UInt8) (ctxIss : ℕ → UInt8) (w : ℕ → F)
    (hw : (uIssueSystem t ctxIss).Holds w) :
    (∀ i < uIssueWitnessBits, w i = bitF (decide (w i = 1))) ∧
      uIssueRel t ctxIss (uIssueK fun i => decide (w i = 1)) (uIssueR fun i => decide (w i = 1)) := by
  set wb : ℕ → Bool := fun i => decide (w i = 1)
  rw [uIssueSystem, System.holds_append, System.holds_append] at hw
  obtain ⟨⟨hb, hK⟩, hout⟩ := hw
  have hbit := bitSystem_sound hb
  refine ⟨hbit, ?_⟩
  obtain ⟨hc1, hc2⟩ := qsKeccak_congr w (ofBits wb) uIssueOffStates 360 (by norm_num)
    (qsInput (F := F) (uIssuePub ctxIss) uIssueMap)
    (eval_qsInput_congr _ _ _ uIssueMap_lt w wb hbit)
    (fun i hi => hbit _ (by simp only [uIssueOffStates, uIssueWitnessBits]; omega))
  have hK' := (holds_congr hc1).1 hK
  unfold uIssueRel
  funext j
  rw [ucom, ← inputState_uIssue]
  refine UInt8.eq_of_byteBit fun b hb' => ?_
  have hj : j.val < 45 := j.isLt
  have hi : 8 * j.val + b < 360 := by omega
  have ho := hout _ (List.mem_map.2 ⟨⟨8 * j.val + b, hi⟩, List.mem_finRange _, rfl⟩)
  simp only [Expr.eval_add, Expr.eval_const] at ho
  have ho' := (CharTwo.add_eq_zero (R := F)).1 ho
  rw [uIssueKeccak, Fin.getElem_fin, hc2 _ hi, qsKeccak_sound _ _ wb _ _ _ hK' _ hi,
    stateBit_eight _ _ _ (by omega) hb'] at ho'
  have := bitF_injective ho'
  rw [this, tBit]
  have e1 : (8 * j.val + b) / 8 = j.val := by omega
  have e2 : (8 * j.val + b) % 8 = b := by omega
  simp only [e1, e2]

end Issue

/-! ## Redeem (`src/moussaka/unbound_redeem.hpp`) -/

section Redeem

/-- `UNBOUND_REDEEM_WIT_OFF_R`, `_NF_KEY`, `_S`, `_COM_STATES`, `_DERIVE_STATES`, `_B`. -/
def uRedeemOffR : ℕ := 0
def uRedeemOffK : ℕ := 16
def uRedeemOffS : ℕ := 32
def uRedeemOffComStates : ℕ := 151
def uRedeemOffDeriveStates : ℕ := 351
def uRedeemOffB : ℕ := 551

/-- `UNBOUND_REDEEM_WITNESS_BITS = 8 · 559`. -/
def uRedeemWitnessBits : ℕ := 8 * 559

/-- `unbound_selector_bit(u) = 8 · UNBOUND_REDEEM_WIT_OFF_B + u`. -/
def uSelBit (u : ℕ) : ℕ := 8 * uRedeemOffB + u

/-- `UNBOUND_REDEEM_COM_TO_WIT`. -/
def uRedeemComMap : Fin 100 → Option ℕ := fun i =>
  if 7 ≤ i.val ∧ i.val < 23 then some (uRedeemOffR + (i.val - 7))
  else if 48 ≤ i.val ∧ i.val < 64 then some (uRedeemOffK + (i.val - 48))
  else none

/-- `UNBOUND_REDEEM_DERIVE_TO_WIT`: the key, at the same witness bytes as in `UCom`'s map. -/
def uRedeemDeriveMap : Fin 100 → Option ℕ := fun i =>
  if 7 ≤ i.val ∧ i.val < 23 then some (uRedeemOffK + (i.val - 7)) else none

/-- `encode_unbound_com_state({}, x.ctx_iss, {})` and `encode_derive_state({}, x.ctx_red)`. -/
def uRedeemComPub (ctxIss : ℕ → UInt8) : State :=
  encodeUnboundComState (fun _ => 0) ctxIss (fun _ => 0)
def uRedeemDerivePub (ctxRed : ℕ → UInt8) : State := encodeDeriveState (fun _ => 0) ctxRed

/-- The decoded opening and key. -/
def uRedeemR (w : ℕ → Bool) : ℕ → UInt8 := fun i => witByte w (uRedeemOffR + i)
def uRedeemK (w : ℕ → Bool) : ℕ → UInt8 := fun i => witByte w (uRedeemOffK + i)

theorem inputState_uRedeemCom (ctxIss : ℕ → UInt8) (w : ℕ → Bool) :
    inputState (uRedeemComPub ctxIss) uRedeemComMap w =
      encodeUnboundComState (uRedeemK w) ctxIss (uRedeemR w) := by
  apply Vector.ext
  intro i hi
  simp only [inputState, Vector.getElem_ofFn]
  unfold uRedeemComMap
  simp only [uRedeemComPub, encodeUnboundComState, Vector.getElem_ofFn, uRedeemR, uRedeemK,
    uRedeemOffR, uRedeemOffK]
  by_cases a1 : i < 7
  · simp [a1, show ¬ 7 ≤ i by omega, show ¬ 48 ≤ i by omega]
  by_cases a2 : i < 23
  · simp [a1, a2, show 7 ≤ i by omega]
  by_cases a3 : i < 48
  · simp [a1, a2, a3, show ¬ 48 ≤ i by omega]
  by_cases a4 : i < 64
  · simp [a1, a2, a3, a4, show 48 ≤ i by omega, show ¬ i < 32 by omega]
  · simp [a1, a2, a3, a4]

theorem inputState_uRedeemDerive (ctxRed : ℕ → UInt8) (w : ℕ → Bool) :
    inputState (uRedeemDerivePub ctxRed) uRedeemDeriveMap w =
      encodeDeriveState (uRedeemK w) ctxRed := by
  apply Vector.ext
  intro i hi
  simp only [inputState, Vector.getElem_ofFn]
  unfold uRedeemDeriveMap
  simp only [uRedeemDerivePub, encodeDeriveState, Vector.getElem_ofFn, uRedeemK, uRedeemOffK]
  by_cases a1 : i < 7
  · simp [a1, show ¬ 7 ≤ i by omega]
  by_cases a2 : i < 23
  · simp [a1, a2, show 7 ≤ i by omega]
  · simp [a1, a2]

variable {F K : Type*}

/-- `prefix` after `u` steps over the unbound selector bits. -/
def uPrefixE [Add F] : ℕ → Expr F
  | 0 => Expr.wit (uSelBit 0)
  | u + 1 => uPrefixE u + Expr.wit (uSelBit (u + 1))

/-- `qs_add_selector_constraints(qs, n, UNBOUND_REDEEM_WIT_OFF_B)` (`circuit.hpp`). -/
def uSelectorSystem [Add F] [Mul F] [One F] (n : ℕ) : System F :=
  (List.range 64).map (fun u =>
      if u < n then bitConstraint (Expr.wit (uSelBit u)) else Expr.wit (uSelBit u)) ++
    (List.range 63).map (fun u => uPrefixE u * Expr.wit (uSelBit (u + 1))) ++
    [uPrefixE 63 + Expr.const 1]

/-- `qs_keccak(UCom input, UNBOUND_REDEEM_WIT_OFF_COM_STATES)`, all 800 output bits. -/
def uRedeemComKeccak [Zero F] [One F] (ctxIss : ℕ → UInt8) : System F × Vector (Expr F) 800 :=
  qsKeccak uRedeemOffComStates 800 le_rfl (qsInput (uRedeemComPub ctxIss) uRedeemComMap)

/-- `qs_keccak(Derive input, UNBOUND_REDEEM_WIT_OFF_DERIVE_STATES, 8 · NF_BYTES)`. -/
def uRedeemDeriveKeccak [Zero F] [One F] (ctxRed : ℕ → UInt8) : System F × Vector (Expr F) 192 :=
  qsKeccak uRedeemOffDeriveStates 192 (by norm_num)
    (qsInput (uRedeemDerivePub ctxRed) uRedeemDeriveMap)

/-- Bit `i` of `nf`. -/
def nfBit (nf : ℕ → UInt8) (i : Fin 192) : Bool := byteBit (nf (i.val / 8)) (i.val % 8)

/-- `qs_add_output_constraints(qs, derive_out, x.nf)`: `out_D[i] + nf_i`, `i < 192`. -/
def nfOutput [Add F] [Mul F] [Zero F] [One F] (nf : ℕ → UInt8) (out : Vector (Expr F) 192) :
    System F :=
  (List.finRange 192).map fun i => out[i] + Expr.const (bitF (nfBit nf i))

/-- `lq` over the unbound selector and preimage offsets. -/
def uLqExpr [Add F] [Mul F] [Zero F] [One F] (β : Fin 8 → F) (toBits : K → Fin 8 → Bool)
    (anchors : List (ℕ → K)) (l : Fin M → F) : Expr F :=
  (List.finRange anchors.length).foldl (fun acc (u : Fin anchors.length) => acc +
    Expr.wit (uSelBit u) *
      evalCombinedPublicMap β toBits N M anchors[u] (fun i => byteLoad β (uRedeemOffS + i)) l)
    (Expr.const 0)

/-- `qs_add_signature_constraint(qs, anchors, b, UNBOUND_REDEEM_WIT_OFF_S, com_out, chal2, …)`. -/
def uRedeemOutput [Add F] [Mul F] [Zero F] [One F] (β : Fin 8 → F) (toBits : K → Fin 8 → Bool)
    (anchors : List (ℕ → K)) (l : Fin M → F) (out : Vector (Expr F) 800) : Expr F :=
  loutExpr β l out + uLqExpr β toBits anchors l

/-- `UnboundRedeemRelation::constraints(qs, {anchors, nf, ctx_iss, ctx_red, _}, chal2)`. -/
def uRedeemSystem [Add F] [Mul F] [Zero F] [One F] (β : Fin 8 → F) (toBits : K → Fin 8 → Bool)
    (anchors : List (ℕ → K)) (nf ctxIss ctxRed : ℕ → UInt8) (l : Fin M → F) : System F :=
  bitSystem (8 * uRedeemOffB) ++ uSelectorSystem anchors.length ++
    (uRedeemComKeccak ctxIss).1 ++ (uRedeemDeriveKeccak ctxRed).1 ++
    nfOutput nf (uRedeemDeriveKeccak ctxRed).2 ++
    [uRedeemOutput β toBits anchors l (uRedeemComKeccak ctxIss).2]

theorem uRedeemSystem_length [Add F] [Mul F] [Zero F] [One F] (β : Fin 8 → F)
    (toBits : K → Fin 8 → Bool) (anchors : List (ℕ → K)) (nf ctxIss ctxRed : ℕ → UInt8)
    (l : Fin M → F) : (uRedeemSystem β toBits anchors nf ctxIss ctxRed l).length = 7929 := by
  simp [uRedeemSystem, bitSystem, uSelectorSystem, uRedeemComKeccak, uRedeemDeriveKeccak,
    nfOutput, qsKeccak_length, uRedeemOffB]

/-- The constraint values computed with sharing (`qsKeccakValues`). -/
def uRedeemValues [Add F] [Mul F] [Zero F] [One F] (β : Fin 8 → F) (toBits : K → Fin 8 → Bool)
    (anchors : List (ℕ → K)) (nf ctxIss ctxRed : ℕ → UInt8) (l : Fin M → F) (w : ℕ → F) :
    List F :=
  let kc := qsKeccakValues w uRedeemOffComStates 800 le_rfl
    ((qsInput (F := F) (uRedeemComPub ctxIss) uRedeemComMap).map (Expr.eval w))
  let kd := qsKeccakValues w uRedeemOffDeriveStates 192 (by norm_num)
    ((qsInput (F := F) (uRedeemDerivePub ctxRed) uRedeemDeriveMap).map (Expr.eval w))
  (bitSystem (8 * uRedeemOffB) ++ uSelectorSystem anchors.length).values w ++ kc.1 ++ kd.1 ++
    ((List.finRange 192).map fun i => kd.2[i] + bitF (nfBit nf i)) ++
    [(uRedeemOutput β toBits anchors l (kc.2.map Expr.const)).eval w]

theorem uRedeemValues_eq [Add F] [Mul F] [Zero F] [One F] (β : Fin 8 → F)
    (toBits : K → Fin 8 → Bool) (anchors : List (ℕ → K)) (nf ctxIss ctxRed : ℕ → UInt8)
    (l : Fin M → F) (w : ℕ → F) :
    uRedeemValues β toBits anchors nf ctxIss ctxRed l w =
      (uRedeemSystem β toBits anchors nf ctxIss ctxRed l).values w := by
  obtain ⟨h1, h2⟩ := qsKeccak_values w uRedeemOffComStates 800 le_rfl
    (qsInput (F := F) (uRedeemComPub ctxIss) uRedeemComMap)
  obtain ⟨d1, d2⟩ := qsKeccak_values w uRedeemOffDeriveStates 192 (by norm_num)
    (qsInput (F := F) (uRedeemDerivePub ctxRed) uRedeemDeriveMap)
  unfold uRedeemValues uRedeemSystem uRedeemComKeccak uRedeemDeriveKeccak
  dsimp only
  rw [System.values] at h1 d1
  simp only [System.values, List.map_append, List.map_singleton, h1, d1, List.append_assoc,
    List.append_cancel_left_eq]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · rw [nfOutput, List.map_map]
    refine List.map_congr_left fun i _ => ?_
    have := congrArg (fun v => v[i]) d2
    simp only [Vector.getElem_map, Fin.getElem_fin] at this
    simp only [Function.comp, Expr.eval_add, Expr.eval_const, Fin.getElem_fin, this]
  · simp only [uRedeemOutput, Expr.eval_add, List.cons.injEq, and_true]
    rw [eval_loutExpr_congr β l _ _ w w fun i hi => ?_]
    have := congrArg (fun v => v[i]) h2
    simp only [Vector.getElem_map] at this
    simp [this]

/-- The UOV target: `UCom(nf_key, ctx_iss, r)` as GF(256) elements. -/
def uRedeemTarget (ofByte : (Fin 8 → Bool) → K) (k ctxIss r : ℕ → UInt8) : Fin M → K :=
  fun j => toK ofByte (ucom k ctxIss r j)

/-- The decoded preimage `σ`. -/
def uRedeemS (ofByte : (Fin 8 → Bool) → K) (w : ℕ → Bool) : ℕ → K := decode ofByte w uRedeemOffS

/-- The unbound redeem relation (`security/moussaka-unbound.md` §2): the selected Anchor's public
map sends `σ` to `UCom(nf_key, ctx_iss, r)` in all 45 components, and `nf = Derive(nf_key,
ctx_red)` on its 24 bytes. -/
def uRedeemRel [Add K] [Mul K] [Zero K] (ofByte : (Fin 8 → Bool) → K) (anchors : List (ℕ → K))
    (nf ctxIss ctxRed k r : ℕ → UInt8) (σ : ℕ → K) (u₀ : ℕ) : Prop :=
  (∃ h : u₀ < anchors.length, publicMap N M anchors[u₀] σ = uRedeemTarget ofByte k ctxIss r) ∧
    ∀ j : Fin NF, nf j.val = derive k ctxRed j

variable [Field F] [CharP F 2] [Add K] [Mul K] [Zero K]
variable {β : Fin 8 → F} {toBits : K → Fin 8 → Bool} {ofByte : (Fin 8 → Bool) → K}

theorem eval_uPrefixE (w : ℕ → F) (u : ℕ) :
    (uPrefixE u).eval w = VoleMole.Moussaka.pre (fun i => w (uSelBit i)) u := by
  induction u with
  | zero => simp [uPrefixE, VoleMole.Moussaka.pre]
  | succ u ih => rw [VoleMole.Moussaka.pre_succ, ← ih]; rfl

/-- The output constraint's value, given bits on `s`, a one-hot selector at `u₀`, and Keccak
outputs equal to the bits of `keccak_p800(encode_unbound_com_state(nf_key, ctx_iss, r))`. -/
theorem eval_uRedeemOutput (hι : IsEmbedding β toBits ofByte) (hβ : β 0 = 1)
    (anchors : List (ℕ → K)) (ctxIss : ℕ → UInt8) (l : Fin M → F)
    (out : Vector (Expr F) 800) (w : ℕ → F) (wb : ℕ → Bool)
    (hs : ∀ n < 8 * N, w (8 * uRedeemOffS + n) = bitF (wb (8 * uRedeemOffS + n)))
    (u₀ : ℕ) (hu₀ : u₀ < anchors.length)
    (hsel : ∀ u < anchors.length, w (uSelBit u) = if u = u₀ then 1 else 0)
    (hout : ∀ i (hi : i < 800), out[i].eval w =
      bitF (stateBit (keccakP800 (encodeUnboundComState (uRedeemK wb) ctxIss (uRedeemR wb))) i)) :
    (uRedeemOutput β toBits anchors l out).eval w =
      ∑ j, l j * (embed β (toBits (publicMap N M anchors[u₀] (uRedeemS ofByte wb) j)) +
        embed β (toBits (uRedeemTarget ofByte (uRedeemK wb) ctxIss (uRedeemR wb) j))) := by
  have hlout : (loutExpr β l out).eval w =
      ∑ j, l j * embed β (toBits (uRedeemTarget ofByte (uRedeemK wb) ctxIss (uRedeemR wb) j)) := by
    rw [loutExpr, eval_linComb]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj : j.val < 45 := j.isLt
    congr 1
    rw [uRedeemTarget, embed_toK hι, ucom]
    set X := keccakP800 (encodeUnboundComState (uRedeemK wb) ctxIss (uRedeemR wb))
    have e : ∀ b < 8, stateBit X (8 * j.val + b) = byteBit X[j.val] b := fun b hb =>
      stateBit_eight X j.val b (by omega) hb
    have e0 : stateBit X (8 * j.val) = byteBit X[j.val] 0 := e 0 (by norm_num)
    simp only [qsByte, Expr.eval_add, Expr.eval_mul, Expr.eval_const]
    rw [hout _ (by omega), hout _ (by omega), hout _ (by omega), hout _ (by omega),
      hout _ (by omega), hout _ (by omega), hout _ (by omega), hout _ (by omega), e0,
      e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num), e 4 (by norm_num),
      e 5 (by norm_num), e 6 (by norm_num), e 7 (by norm_num), Fin.sum_univ_eight, hβ]
    have h3 : ((3 : Fin 8) : ℕ) = 3 := rfl
    have h4 : ((4 : Fin 8) : ℕ) = 4 := rfl
    have h5 : ((5 : Fin 8) : ℕ) = 5 := rfl
    have h6 : ((6 : Fin 8) : ℕ) = 6 := rfl
    have h7 : ((7 : Fin 8) : ℕ) = 7 := rfl
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, h3, h4, h5, h6, h7]
    ring
  have hlq : (uLqExpr β toBits anchors l).eval w =
      ∑ j, l j * embed β (toBits (publicMap N M anchors[u₀] (uRedeemS ofByte wb) j)) := by
    rw [uLqExpr, eval_foldl_add, Expr.eval_const, zero_add, ← Fin.sum_univ_def,
      Finset.sum_eq_single ⟨u₀, hu₀⟩]
    · simp only [Expr.eval_mul, Expr.eval_wit, hsel u₀ hu₀, ite_true, one_mul]
      exact eval_evalCombinedPublicMap_of_bits hι N M anchors[u₀] l _ w wb hs
    · intro u _ hu
      have : u.val ≠ u₀ := fun h => hu (Fin.ext h)
      simp only [Expr.eval_mul, Expr.eval_wit, hsel u.val u.isLt, this, ite_false, zero_mul]
    · exact fun h => absurd (Finset.mem_univ _) h
  rw [uRedeemOutput, Expr.eval_add, hlout, hlq, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem mem_uSelector_bit (n u : ℕ) (hu : u < 64) :
    (if u < n then bitConstraint (Expr.wit (uSelBit u)) else Expr.wit (uSelBit u)) ∈
      (uSelectorSystem n : System F) :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_map.2 ⟨u, List.mem_range.2 hu, rfl⟩))

theorem mem_uSelector_parity (n u : ℕ) (hu : u < 63) :
    uPrefixE u * Expr.wit (uSelBit (u + 1)) ∈ (uSelectorSystem n : System F) :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨u, List.mem_range.2 hu, rfl⟩))

theorem mem_uSelector_weight (n : ℕ) :
    uPrefixE 63 + Expr.const 1 ∈ (uSelectorSystem n : System F) :=
  List.mem_append_right _ (List.mem_singleton_self _)

/-- **Selector soundness** at the unbound selector offset. -/
theorem uSelector_sound [DecidableEq F] (n : ℕ) (w : ℕ → F) (h : (uSelectorSystem n).Holds w) :
    (∀ u < 64, w (uSelBit u) = bitF (decide (w (uSelBit u) = 1))) ∧
      ∃ u₀ < n, ∀ u < 64, w (uSelBit u) = if u = u₀ then 1 else 0 := by
  have hzero : ∀ u < 64, n ≤ u → w (uSelBit u) = 0 := fun u hu hnu => by
    have := h _ (mem_uSelector_bit n u hu)
    simpa only [show ¬ u < n by omega, ↓reduceIte, Expr.eval_wit] using this
  have hbit : ∀ u < 64, w (uSelBit u) = bitF (decide (w (uSelBit u) = 1)) := by
    intro u hu
    by_cases hnu : u < n
    · have := h _ (mem_uSelector_bit n u hu)
      simp only [hnu, ↓reduceIte] at this
      exact eq_bitF_of_bitConstraint this
    · rw [hzero u hu (by omega)]; simp [bitF]
  refine ⟨hbit, ?_⟩
  set b : ℕ → F := fun u => w (uSelBit u)
  have hpar : ∀ u, u + 1 < 64 → VoleMole.Moussaka.pre b u * b (u + 1) = 0 := fun u hu => by
    have := h _ (mem_uSelector_parity n u (by omega))
    rwa [Expr.eval_mul, eval_uPrefixE] at this
  have hsum : ∑ i ∈ range 64, b i = 1 := by
    have := h _ (mem_uSelector_weight n)
    rw [Expr.eval_add, eval_uPrefixE, Expr.eval_const] at this
    exact (CharTwo.add_eq_zero (R := F)).1 this
  obtain ⟨i, hi, hbi, hz⟩ := VoleMole.Moussaka.selector_one_hot b 64 hpar hsum
  have hin : i < n := by
    by_contra hc
    have := hzero i hi (by omega)
    simp only [b] at hbi
    rw [this] at hbi
    exact zero_ne_one hbi
  refine ⟨i, hin, fun u hu => ?_⟩
  split_ifs with hui
  · rw [hui]; exact hbi
  · exact hz u hu hui

/-- **Selector completeness** at the unbound selector offset. -/
theorem uSelector_complete (n : ℕ) (w : ℕ → Bool) (u₀ : ℕ) (hu₀ : u₀ < n) (hn : n ≤ 64)
    (hsel : ∀ u < 64, w (uSelBit u) = decide (u = u₀)) :
    (uSelectorSystem n).Holds (ofBits w : ℕ → F) := by
  have hpre : ∀ u < 64, (uPrefixE u).eval (ofBits w : ℕ → F) = if u₀ ≤ u then 1 else 0 := by
    intro u
    induction u with
    | zero =>
      intro _
      simp only [uPrefixE, Expr.eval_wit, ofBits, hsel 0 (by norm_num), bitF]
      by_cases h0 : u₀ = 0 <;> simp [h0, eq_comm]
    | succ u ih =>
      intro hu
      simp only [uPrefixE, Expr.eval_add, Expr.eval_wit, ofBits, hsel (u + 1) hu, bitF,
        ih (by omega)]
      by_cases h1 : u₀ ≤ u
      · simp [h1, show u₀ ≤ u + 1 by omega, show u + 1 ≠ u₀ by omega]
      · by_cases h2 : u₀ = u + 1
        · simp [h2]
        · simp [h1, show ¬ u₀ ≤ u + 1 by omega, Ne.symm h2]
  intro e he
  simp only [uSelectorSystem, List.mem_append, List.mem_map, List.mem_range,
    List.mem_singleton] at he
  rcases he with (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) | rfl
  · split_ifs with hnu
    · exact bitConstraint_bits w _
    · simp [ofBits, hsel u hu, bitF, show u ≠ u₀ by omega]
  · rw [Expr.eval_mul, hpre u (by omega), Expr.eval_wit, ofBits, hsel (u + 1) (by omega)]
    by_cases h1 : u₀ ≤ u
    · simp [h1, show u + 1 ≠ u₀ by omega, bitF]
    · simp [h1]
  · rw [Expr.eval_add, hpre 63 (by norm_num), Expr.eval_const]
    simp only [show u₀ ≤ 63 by omega, ↓reduceIte]
    exact CharTwo.add_self_eq_zero _

theorem uRedeemComMap_lt : ∀ i b, uRedeemComMap i = some b → b < 8 * uRedeemOffB / 8 := by
  intro i b h
  simp only [uRedeemComMap, uRedeemOffR, uRedeemOffK] at h
  split_ifs at h <;> simp only [Option.some.injEq] at h <;> simp only [uRedeemOffB] <;> omega

theorem uRedeemDeriveMap_lt : ∀ i b, uRedeemDeriveMap i = some b → b < 8 * uRedeemOffB / 8 := by
  intro i b h
  simp only [uRedeemDeriveMap, uRedeemOffK] at h
  split_ifs at h
  simp only [Option.some.injEq] at h
  simp only [uRedeemOffB]; omega

/-- The `nf` output constraints hold iff the first 24 bytes of the `Derive` output are `nf`, given
Keccak outputs equal to the bits of `keccak_p800(X)`. -/
theorem nfOutput_holds_iff (nf : ℕ → UInt8) (out : Vector (Expr F) 192) (w : ℕ → F) (X : State)
    (hout : ∀ i (hi : i < 192), out[i].eval w = bitF (stateBit X i)) :
    (nfOutput nf out).Holds w ↔ ∀ j : Fin NF, nf j.val = X[j.val] := by
  constructor
  · intro h j
    refine UInt8.eq_of_byteBit fun b hb => ?_
    have hj : j.val < 24 := j.isLt
    have hi : 8 * j.val + b < 192 := by omega
    have ho := h _ (List.mem_map.2 ⟨⟨8 * j.val + b, hi⟩, List.mem_finRange _, rfl⟩)
    simp only [Expr.eval_add, Expr.eval_const] at ho
    have ho' := (CharTwo.add_eq_zero (R := F)).1 ho
    rw [Fin.getElem_fin, hout _ hi, stateBit_eight _ _ _ (by omega) hb] at ho'
    have := bitF_injective ho'
    rw [this, nfBit]
    have e1 : (8 * j.val + b) / 8 = j.val := by omega
    have e2 : (8 * j.val + b) % 8 = b := by omega
    simp only [e1, e2]
  · intro h e he
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
    have hi := i.isLt
    rw [Expr.eval_add, Expr.eval_const, Fin.getElem_fin, hout _ hi]
    have hb : stateBit X i.val = nfBit nf i := by
      rw [stateBit_eq _ _ (by omega), nfBit, h ⟨i.val / 8, by simp only [NF]; omega⟩]
    rw [hb]; exact CharTwo.add_self_eq_zero _

/-- **Completeness.** A bit vector with arbitrary `r`, `nf_key`, `s`, honest committed states of
both Keccak instances, a one-hot selector `b = e_{u₀}` (`u₀ < n ≤ 64`), and a witness of the
unbound redeem relation satisfies every constraint, for every `l`. -/
theorem uRedeem_complete (hι : IsEmbedding β toBits ofByte) (hβ : β 0 = 1)
    (anchors : List (ℕ → K)) (hn : anchors.length ≤ 64) (nf ctxIss ctxRed : ℕ → UInt8)
    (l : Fin M → F) (w : ℕ → Bool)
    (hc5 : ∀ i < 800, w (8 * uRedeemOffComStates + i) =
      stateBit (keccakP800Rounds 0 5 (encodeUnboundComState (uRedeemK w) ctxIss (uRedeemR w))) i)
    (hc9 : ∀ i < 800, w (8 * (uRedeemOffComStates + 100) + i) =
      stateBit (keccakP800Rounds 0 9 (encodeUnboundComState (uRedeemK w) ctxIss (uRedeemR w))) i)
    (hd5 : ∀ i < 800, w (8 * uRedeemOffDeriveStates + i) =
      stateBit (keccakP800Rounds 0 5 (encodeDeriveState (uRedeemK w) ctxRed)) i)
    (hd9 : ∀ i < 800, w (8 * (uRedeemOffDeriveStates + 100) + i) =
      stateBit (keccakP800Rounds 0 9 (encodeDeriveState (uRedeemK w) ctxRed)) i)
    (u₀ : ℕ) (hsel : ∀ u < 64, w (uSelBit u) = decide (u = u₀))
    (hrel : uRedeemRel ofByte anchors nf ctxIss ctxRed (uRedeemK w) (uRedeemR w)
      (uRedeemS ofByte w) u₀) :
    (uRedeemSystem β toBits anchors nf ctxIss ctxRed l).Holds (ofBits w) := by
  obtain ⟨⟨hu₀, hP⟩, hnf⟩ := hrel
  rw [← inputState_uRedeemCom] at hc5 hc9
  rw [← inputState_uRedeemDerive] at hd5 hd9
  have hKc := qsKeccak_complete (F := F) (uRedeemComPub ctxIss) uRedeemComMap w
    uRedeemOffComStates 800 le_rfl hc5 hc9
  have hKd := qsKeccak_complete (F := F) (uRedeemDerivePub ctxRed) uRedeemDeriveMap w
    uRedeemOffDeriveStates 192 (by norm_num) hd5 hd9
  rw [uRedeemSystem, System.holds_append, System.holds_append, System.holds_append,
    System.holds_append, System.holds_append]
  refine ⟨⟨⟨⟨⟨bitSystem_holds _ w, uSelector_complete _ w u₀ hu₀ hn hsel⟩, hKc⟩, hKd⟩, ?_⟩, ?_⟩
  · rw [nfOutput_holds_iff nf _ (ofBits w) (keccakP800 (encodeDeriveState (uRedeemK w) ctxRed))
      (fun i hi => by
        rw [uRedeemDeriveKeccak, qsKeccak_sound _ _ w _ _ _ hKd i hi, inputState_uRedeemDerive])]
    exact fun j => hnf j
  · intro e he
    rw [List.mem_singleton] at he
    subst he
    rw [eval_uRedeemOutput hι hβ anchors ctxIss l _ (ofBits w) w (fun _ _ => rfl) u₀ hu₀
      (fun u hu => by simp [ofBits, hsel u (by omega), bitF])
      (fun i hi => by
        rw [uRedeemComKeccak, qsKeccak_sound _ _ w _ _ _ hKc i hi, inputState_uRedeemCom]), hP]
    simp [CharTwo.add_self_eq_zero]

/-- **Soundness (deterministic).** If the constraints hold at any committed values `w ∈ F^ℓ` and
`n ≤ MAX_ANCHORS`, then every witness bit is a bit, the selector is `e_{u₀}` for some `u₀ < n`,
`nf = Derive(nf_key, ctx_red)` for the decoded key, and the decoded `(nf_key, r, σ)` satisfy the
combined equation `Σ_j l_j (ι(P_{u₀}(σ)_j) + ι(UCom(nf_key, ctx_iss, r)_j)) = 0`. -/
theorem uRedeem_sound [DecidableEq F] (hι : IsEmbedding β toBits ofByte) (hβ : β 0 = 1)
    (anchors : List (ℕ → K)) (hn : anchors.length ≤ 64) (nf ctxIss ctxRed : ℕ → UInt8)
    (l : Fin M → F) (w : ℕ → F)
    (hw : (uRedeemSystem β toBits anchors nf ctxIss ctxRed l).Holds w) :
    (∀ i < uRedeemWitnessBits, w i = bitF (decide (w i = 1))) ∧
      (∀ j : Fin NF, nf j.val = derive (uRedeemK fun i => decide (w i = 1)) ctxRed j) ∧
      ∃ u₀, ∃ hu₀ : u₀ < anchors.length,
        (∀ u < 64, decide (w (uSelBit u) = 1) = decide (u = u₀)) ∧
        ∑ j, l j * (embed β (toBits (publicMap N M anchors[u₀]
            (uRedeemS ofByte fun i => decide (w i = 1)) j)) +
          embed β (toBits (uRedeemTarget ofByte (uRedeemK fun i => decide (w i = 1)) ctxIss
            (uRedeemR fun i => decide (w i = 1)) j))) = 0 := by
  set wb : ℕ → Bool := fun i => decide (w i = 1)
  rw [uRedeemSystem, System.holds_append, System.holds_append, System.holds_append,
    System.holds_append, System.holds_append] at hw
  obtain ⟨⟨⟨⟨⟨hb, hs⟩, hKc⟩, hKd⟩, hnfo⟩, hout⟩ := hw
  have hbit1 := bitSystem_sound hb
  obtain ⟨hbit2, u₀, hu₀, hsel⟩ := uSelector_sound _ w hs
  have hbit : ∀ i < uRedeemWitnessBits, w i = bitF (wb i) := by
    intro i hi
    by_cases h : i < 8 * uRedeemOffB
    · exact hbit1 i h
    · have := hbit2 (i - 8 * uRedeemOffB)
        (by simp only [uRedeemWitnessBits, uRedeemOffB] at *; omega)
      rwa [uSelBit, show 8 * uRedeemOffB + (i - 8 * uRedeemOffB) = i by omega] at this
  have hsel' : ∀ u < 64, wb (uSelBit u) = decide (u = u₀) := fun u hu => by
    simp only [wb, hsel u hu]
    split_ifs with h <;> simp [h]
  obtain ⟨hc1, hc2⟩ := qsKeccak_congr w (ofBits wb) uRedeemOffComStates 800 le_rfl
    (qsInput (F := F) (uRedeemComPub ctxIss) uRedeemComMap)
    (eval_qsInput_congr _ _ _ uRedeemComMap_lt w wb hbit1)
    (fun i hi => hbit1 _ (by simp only [uRedeemOffComStates, uRedeemOffB]; omega))
  have hKc' := (holds_congr hc1).1 hKc
  obtain ⟨hd1, hd2⟩ := qsKeccak_congr w (ofBits wb) uRedeemOffDeriveStates 192 (by norm_num)
    (qsInput (F := F) (uRedeemDerivePub ctxRed) uRedeemDeriveMap)
    (eval_qsInput_congr _ _ _ uRedeemDeriveMap_lt w wb hbit1)
    (fun i hi => hbit1 _ (by simp only [uRedeemOffDeriveStates, uRedeemOffB]; omega))
  have hKd' := (holds_congr hd1).1 hKd
  refine ⟨hbit, ?_, u₀, by omega, hsel', ?_⟩
  · have := (nfOutput_holds_iff nf _ w (keccakP800 (encodeDeriveState (uRedeemK wb) ctxRed))
      (fun i hi => by
        rw [uRedeemDeriveKeccak, hd2 i hi, qsKeccak_sound _ _ wb _ _ _ hKd' i hi,
          inputState_uRedeemDerive])).1 hnfo
    exact fun j => this j
  · have := hout _ (List.mem_singleton_self _)
    rwa [eval_uRedeemOutput hι hβ anchors ctxIss l _ w wb
      (fun n hn => hbit _ (by simp only [uRedeemOffS, uRedeemWitnessBits, N] at *; omega)) u₀
      (by omega) (fun u hu => hsel u (by omega))
      (fun i hi => by
        rw [uRedeemComKeccak, hc2 i hi, qsKeccak_sound _ _ wb _ _ _ hKc' i hi,
          inputState_uRedeemCom])] at this

open Classical in
/-- **Soundness, end to end.** Fix the committed values `w ∈ F^ℓ` and the instance before drawing
`l`, with `n ≤ MAX_ANCHORS`. Either `w` is a bit vector on all `8·559` witness bits whose selector
is `e_{u₀}` with `u₀ < n` and whose `(nf_key, r, σ)` satisfy the unbound redeem relation
(`P_{anchors[u₀]}(σ) = UCom(nf_key, ctx_iss, r)` and `nf = Derive(nf_key, ctx_red)`), or at most a
`1/|F|` fraction of the `l` make every constraint hold. -/
theorem uRedeem_sound_card [Fintype F] [DecidableEq F] (hι : IsEmbedding β toBits ofByte)
    (hβ : β 0 = 1) (anchors : List (ℕ → K)) (hn : anchors.length ≤ 64)
    (nf ctxIss ctxRed : ℕ → UInt8) (w : ℕ → F) :
    (∃ wb : ℕ → Bool, (∀ i < uRedeemWitnessBits, w i = bitF (wb i)) ∧
        ∃ u₀, (∀ u < 64, wb (uSelBit u) = decide (u = u₀)) ∧
          uRedeemRel ofByte anchors nf ctxIss ctxRed (uRedeemK wb) (uRedeemR wb)
            (uRedeemS ofByte wb) u₀) ∨
      #{l : Fin M → F | (uRedeemSystem β toBits anchors nf ctxIss ctxRed l).Holds w} *
        Fintype.card F ≤ Fintype.card (Fin M → F) := by
  set wb : ℕ → Bool := fun i => decide (w i = 1)
  by_cases hS : #{l : Fin M → F | (uRedeemSystem β toBits anchors nf ctxIss ctxRed l).Holds w} = 0
  · right; rw [hS, zero_mul]; exact Nat.zero_le _
  obtain ⟨l₀, hl₀⟩ := Finset.card_ne_zero.1 hS
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl₀
  obtain ⟨hbit, hnf, u₀, hu₀, hsel, -⟩ := uRedeem_sound hι hβ anchors hn nf ctxIss ctxRed l₀ w hl₀
  by_cases hP : publicMap N M anchors[u₀] (uRedeemS ofByte wb) =
      uRedeemTarget ofByte (uRedeemK wb) ctxIss (uRedeemR wb)
  · exact Or.inl ⟨wb, hbit, u₀, hsel, ⟨hu₀, hP⟩, hnf⟩
  right
  rw [← uov_card_bad hι hP]
  refine Nat.mul_le_mul_right _ (Finset.card_le_card fun l hl => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
  obtain ⟨-, -, u₁, hu₁, hsel₁, hcomb⟩ := uRedeem_sound hι hβ anchors hn nf ctxIss ctxRed l w hl
  have : u₁ = u₀ := by
    have h1 := hsel₁ u₀ (by omega)
    rw [hsel u₀ (by omega)] at h1
    simpa [eq_comm] using h1
  subst this
  exact hcomb

end Redeem

end VoleMole.Arith.MoussakaUnbound
