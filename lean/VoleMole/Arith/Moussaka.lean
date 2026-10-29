import VoleMole.Arith.UOV
import VoleMole.Arith.Keccak
import VoleMole.Protocols.Moussaka

/-!
# Moussaka issue and redeem (`src/moussaka/issue.hpp`, `src/moussaka/redeem.hpp`)

Executable models of `moussaka::detail::IssueRelation::constraints` (`issue.hpp:169-191`) and
`RedeemRelation::constraints` (`redeem.hpp:202-271`), with completeness and soundness against the
relations that `lean/docs/security/moussaka.md` §1 and §3.1 use:

* **issue** (`L7-keccak.md` §4.1): `t = Com(nf, ctx_iss, ctx_red, r)`, with
  `Com(x) = keccak_p800(encode_com_state(x))[0..45)` (`src/moussaka/moussaka.cpp:89-95`);
* **redeem** (`L7-uov.md` §5, `L7-keccak.md` §4.2): a one-hot selector `b = e_{u₀}` with
  `u₀ < |anchors|`, and `P_{anchors[u₀]}(σ) = Com(nf, ctx_iss, ctx_red, r)` in all 45 components.

## Model

* Commitment input (`src/moussaka/commit.hpp:33-48`, `encodeComState`):
  `"mous" ‖ 0x00 ‖ "c0" ‖ r ‖ 0⁹ ‖ ctx_iss ‖ ctx_red ‖ nf ‖ 0¹²` (offsets 0, 7, 32, 48, 64, 88).
  The DST bytes `make_dst("mous", VERSION = 0, 'c', '0')` (`src/dst.hpp:33`) are `comDst`; the
  harness checks the whole public state against the C++ (`keccak_in_0`).
* Issue witness (`issue.hpp:58-63`): bytes `r = [0,16)`, `ctx_red = [16,32)`, `nf = [32,56)`, the
  committed Keccak states at byte 56 (`2048` bits). Input map `COM_TO_WIT` (`:67-81`) is
  `issueMap`; the public state `encode_com_state({}, ctx_iss, {}, {})` is `issuePub`.
  Constraints: 2048 bit constraints, `qs_keccak(…, 56, 360)`'s 1600 constraints, then
  `out[i] + t_i` for `i < 360` (`issue.hpp:188-190`).
* Redeem witness (`redeem.hpp:74-84`): `r = [0,16)`, `s = [16,135)`, states at 135, selector bit
  `b[u]` at witness bit `8·335 + u` (`selBit`). Input map `REDEEM_COM_TO_WIT` (`:88-95`) is
  `redeemMap`; public state `encode_com_state(nf, ctx_iss, ctx_red, {})`. Constraints, in order
  (`REDEEM_NUM_CONSTRAINTS = 4409` for `MAX_ANCHORS = 64`, `:100-106`):
  1. bit constraints on the first `8·335 = 2680` bits (`:219-221`);
  2. for `u < 64`: `bitConstraint b[u]` if `u < n`, else `b[u]` (`:224-232`);
  3. parity `prefix_u · b[u+1]` for `u < 63`, `prefix_0 = b[0]`, `prefix_{u+1} = prefix_u + b[u+1]`
     (`:235-239`), and weight `prefix_63 + 1` (`:242`);
  4. `qs_keccak(…, 135)`'s 1600 constraints (`:245-249`);
  5. `lout + lq` with `lq = 0 + Σ_{u<n} b[u] · l(P_u(s))`, `lout = 0 + Σ_k l_k · qs_byte(out, k)`
     (`:250-270`).
* `l : Fin 45 → F` is `Combination(chal2, MOUSSAKA_REDEEM_COMBINE_DST)`, passed as an argument.
* Values of degree lifts and conversions are the identity (`L7-uov.md` §0).

## Main results

* Wiring: `inputState_issue`, `inputState_redeem`: the input that `qs_input` builds is
  `encode_com_state` of the decoded witness fields (`inputState` of the Keccak module).
* Issue: `issueSystem_length` (4008), `issue_complete`, `issue_sound` (deterministic; no
  combination challenge).
* Redeem: `redeemSystem_length` (4409), `redeem_complete`, `redeem_sound` (bits, unique one-hot
  selector below `n`, and the combined equation), `redeem_card_bad`, and the end-to-end
  `redeem_sound_card`: for committed values fixed before `l`, either they encode a witness of the
  redeem relation, or at most a `1/|F|` fraction of the `l` make every constraint hold.
* Executable values with sharing: `issueValues_eq`, `redeemValues_eq` (equal to `System.values`).
-/

open Finset

set_option linter.unusedSectionVars false

namespace VoleMole.Arith.Moussaka

open VoleMole.Arith UOV Keccak

/-! ## Constants and the commitment -/

/-- `uov::N`, `uov::M` (`include/vole_mole/uov.hpp`). -/
abbrev N : ℕ := 119
abbrev M : ℕ := 45

/-- `MOUSSAKA_COM_DST = make_dst("mous", VERSION, 'c', '0')` (`src/dst.hpp:33`). -/
def comDst : List UInt8 := [0x6d, 0x6f, 0x75, 0x73, 0x00, 0x63, 0x30]

/-- `encode_com_state(nf, ctx_iss, ctx_red, r)` (`src/moussaka/commit.hpp:40-48`), with
`COM_OFF_R = 7`, `COM_OFF_CTX_ISS = 32`, `COM_OFF_CTX_RED = 48`, `COM_OFF_NF = 64`. -/
def encodeComState (nf ctxIss ctxRed r : ℕ → UInt8) : State :=
  Vector.ofFn fun k =>
    if k.val < 7 then comDst.getD k.val 0
    else if k.val < 23 then r (k.val - 7)
    else if k.val < 32 then 0
    else if k.val < 48 then ctxIss (k.val - 32)
    else if k.val < 64 then ctxRed (k.val - 48)
    else if k.val < 88 then nf (k.val - 64)
    else 0

/-- `Com(nf, ctx_iss, ctx_red, r)`: the first 45 bytes of `keccak_p800(encode_com_state(…))`
(`src/moussaka/moussaka.cpp:89-95`). -/
def com (nf ctxIss ctxRed r : ℕ → UInt8) (k : Fin M) : UInt8 :=
  (keccakP800 (encodeComState nf ctxIss ctxRed r))[k.val]

/-- Bit `j` of a byte: `(x >> j) & 1`. -/
def byteBit (x : UInt8) (j : ℕ) : Bool := x.toBitVec.getLsbD j

theorem stateBit_eight (s : State) (k j : ℕ) (hk : k < 100) (hj : j < 8) :
    stateBit s (8 * k + j) = byteBit s[k] j := by
  have h1 : (8 * k + j) / 8 = k := by omega
  have h2 : (8 * k + j) % 8 = j := by omega
  simp [stateBit, byteBit, h1, h2, hk]

theorem stateBit_eq (s : State) (i : ℕ) (hi : i < 800) :
    stateBit s i = byteBit s[i / 8] (i % 8) := by
  simp [stateBit, byteBit, show i / 8 < 100 by omega]

theorem UInt8.eq_of_byteBit {x y : UInt8} (h : ∀ j < 8, byteBit x j = byteBit y j) : x = y := by
  apply UInt8.toBitVec_inj.mp
  exact BitVec.eq_of_getLsbD_eq fun j hj => h j hj

theorem bitF_injective {F : Type*} [Field F] {a b : Bool} (h : (bitF a : F) = bitF b) : a = b := by
  cases a <;> cases b <;> simp_all [bitF]

/-! ## Shared lemmas -/

section Shared

variable {F : Type*}

theorem holds_iff_values [Add F] [Mul F] [Zero F] (cs : System F) (w : ℕ → F) :
    cs.Holds w ↔ ∀ v ∈ cs.values w, v = 0 := by
  simp [System.Holds, System.values]

theorem holds_congr [Add F] [Mul F] [Zero F] {cs : System F} {w w' : ℕ → F}
    (h : cs.values w = cs.values w') : cs.Holds w ↔ cs.Holds w' := by
  rw [holds_iff_values, holds_iff_values, h]

/-- `qs_keccak` reads the witness only through the two committed states. -/
theorem qsKeccakG_layout_congr {T : Type*} (O : BitOps T) (wit wit' : ℕ → T)
    (final wOff n : ℕ) (hn : n ≤ 800) (s : Vector T 800)
    (h : ∀ i < 1600, wit (8 * wOff + i) = wit' (8 * wOff + i)) :
    qsKeccakG O wit layout final wOff n hn s = qsKeccakG O wit' layout final wOff n hn s := by
  have h0 : witState wit (8 * (wOff + 100 * 0)) = witState wit' (8 * (wOff + 100 * 0)) := by
    ext i hi
    simp only [witState, Vector.getElem_ofFn]
    have := h i (by omega)
    rwa [show 8 * (wOff + 100 * 0) + i = 8 * wOff + i by ring]
  have h1 : witState wit (8 * (wOff + 100 * (0 + 1))) =
      witState wit' (8 * (wOff + 100 * (0 + 1))) := by
    ext i hi
    simp only [witState, Vector.getElem_ofFn]
    have := h (800 + i) (by omega)
    rwa [show 8 * (wOff + 100 * (0 + 1)) + i = 8 * wOff + (800 + i) by ring]
  simp only [qsKeccakG, layout, segmentConstraints, segmentConstraint, h0, h1]

/-- Two committed-value vectors that agree on the input and on the committed states give the same
Keccak constraint values and outputs. -/
theorem qsKeccak_congr [Add F] [Mul F] [One F] (w w' : ℕ → F) (wOff n : ℕ) (hn : n ≤ 800)
    (input : Vector (Expr F) 800) (hin : ∀ i (hi : i < 800), input[i].eval w = input[i].eval w')
    (hw : ∀ i < 1600, w (8 * wOff + i) = w' (8 * wOff + i)) :
    (qsKeccak wOff n hn input).1.values w = (qsKeccak wOff n hn input).1.values w' ∧
      ∀ i (hi : i < n),
        (qsKeccak wOff n hn input).2[i].eval w = (qsKeccak wOff n hn input).2[i].eval w' := by
  obtain ⟨a1, a2⟩ := qsKeccak_values w wOff n hn input
  obtain ⟨b1, b2⟩ := qsKeccak_values w' wOff n hn input
  have hinp : input.map (Expr.eval w) = input.map (Expr.eval w') := by
    ext i hi; simp [hin i hi]
  have hg : qsKeccakValues w wOff n hn (input.map (Expr.eval w')) =
      qsKeccakValues w' wOff n hn (input.map (Expr.eval w')) :=
    qsKeccakG_layout_congr _ _ _ _ _ _ _ _ hw
  refine ⟨by rw [a1, b1, hinp, hg], fun i hi => ?_⟩
  have e1 := congrArg (fun v => v[i]) a2
  have e2 := congrArg (fun v => v[i]) b2
  simp only [Vector.getElem_map] at e1 e2
  rw [e1, e2, hinp, hg]

theorem eval_foldl_add [Field F] {α : Type*} (f : α → Expr F) (L : List α) (a : Expr F)
    (w : ℕ → F) :
    (L.foldl (fun acc x => acc + f x) a).eval w = a.eval w + (L.map fun x => (f x).eval w).sum := by
  induction L generalizing a with
  | nil => simp
  | cons x L ih => simp [ih, add_assoc]

end Shared

/-! ## Issue (`src/moussaka/issue.hpp`) -/

section Issue

/-- `WIT_OFF_R`, `WIT_OFF_CTX_RED`, `WIT_OFF_NF`, `WIT_OFF_STATES` (`issue.hpp:58-61`). -/
def issueOffR : ℕ := 0
def issueOffCtxRed : ℕ := 16
def issueOffNf : ℕ := 32
def issueOffStates : ℕ := 56

/-- `ISSUE_WITNESS_BITS = 8 · 256` (`issue.hpp:62-63`). -/
def issueWitnessBits : ℕ := 2048

/-- `COM_TO_WIT` (`issue.hpp:67-81`). -/
def issueMap : Fin 100 → Option ℕ := fun k =>
  if 7 ≤ k.val ∧ k.val < 23 then some (issueOffR + (k.val - 7))
  else if 48 ≤ k.val ∧ k.val < 64 then some (issueOffCtxRed + (k.val - 48))
  else if 64 ≤ k.val ∧ k.val < 88 then some (issueOffNf + (k.val - 64))
  else none

/-- `encode_com_state({}, x.ctx_iss, {}, {})` (`issue.hpp:183`). -/
def issuePub (ctxIss : ℕ → UInt8) : State := encodeComState (fun _ => 0) ctxIss (fun _ => 0) (fun _ => 0)

/-- Decoded witness fields. -/
def issueR (w : ℕ → Bool) : ℕ → UInt8 := fun i => witByte w (issueOffR + i)
def issueCtxRed (w : ℕ → Bool) : ℕ → UInt8 := fun i => witByte w (issueOffCtxRed + i)
def issueNf (w : ℕ → Bool) : ℕ → UInt8 := fun i => witByte w (issueOffNf + i)

/-- **Input wiring** (`L7-keccak.md` §4.1, test `KeccakInputIsCommitmentInput`): the Keccak input
built by `qs_input(encode_com_state({}, ctx_iss, {}, {}), COM_TO_WIT)` is
`encode_com_state(nf, ctx_iss, ctx_red, r)` of the decoded witness. -/
theorem inputState_issue (ctxIss : ℕ → UInt8) (w : ℕ → Bool) :
    inputState (issuePub ctxIss) issueMap w =
      encodeComState (issueNf w) ctxIss (issueCtxRed w) (issueR w) := by
  apply Vector.ext
  intro k hk
  simp only [inputState, Vector.getElem_ofFn]
  unfold issueMap
  simp only [issuePub, encodeComState, Vector.getElem_ofFn, issueR, issueCtxRed, issueNf,
    issueOffR, issueOffCtxRed, issueOffNf]
  by_cases a1 : k < 7
  · simp [a1, show ¬ 7 ≤ k by omega, show ¬ 48 ≤ k by omega, show ¬ 64 ≤ k by omega]
  by_cases a2 : k < 23
  · simp [a1, a2, show 7 ≤ k by omega]
  by_cases a3 : k < 48
  · simp [a1, a2, a3, show k < 64 by omega, show ¬ 48 ≤ k by omega, show ¬ 64 ≤ k by omega]
  by_cases a4 : k < 64
  · simp [a1, a2, a3, a4, show 48 ≤ k by omega, show ¬ k < 32 by omega]
  by_cases a5 : k < 88
  · simp [a1, a2, a3, a4, a5, show 64 ≤ k by omega, show ¬ k < 32 by omega]
  · simp [a1, a2, a3, a4, a5]

variable {F : Type*}

/-- The Keccak part: `qs_keccak(qs_input(…), WIT_OFF_STATES, 8M)` (`issue.hpp:182-184`). -/
def issueKeccak [Zero F] [One F] (ctxIss : ℕ → UInt8) : System F × Vector (Expr F) 360 :=
  qsKeccak issueOffStates 360 (by norm_num) (qsInput (issuePub ctxIss) issueMap)

/-- Bit `i` of `t` (`(x.t[i / 8] >> (i % 8)) & 1`). -/
def tBit (t : Fin M → UInt8) (i : Fin 360) : Bool :=
  byteBit (t ⟨i.val / 8, by have := i.isLt; show i.val / 8 < 45; omega⟩) (i.val % 8)

/-- The bit constraints on the first `B` witness bits. -/
def bitSystem [One F] (B : ℕ) : System F := (List.range B).map fun i => bitConstraint (Expr.wit i)

/-- The output constraints `out[i] + t_i`, `i < 360` (`issue.hpp:188-190`). -/
def issueOutput [Add F] [Mul F] [Zero F] [One F] (t : Fin M → UInt8) (out : Vector (Expr F) 360) :
    System F :=
  (List.finRange 360).map fun i => out[i] + Expr.const (bitF (tBit t i))

/-- `IssueRelation::constraints(qs, {t, ctx_iss}, chal2)` (`issue.hpp:169-191`). -/
def issueSystem [Add F] [Mul F] [Zero F] [One F] (t : Fin M → UInt8) (ctxIss : ℕ → UInt8) :
    System F :=
  bitSystem issueWitnessBits ++ (issueKeccak ctxIss).1 ++ issueOutput t (issueKeccak ctxIss).2

theorem issueSystem_length [Add F] [Mul F] [Zero F] [One F] (t : Fin M → UInt8)
    (ctxIss : ℕ → UInt8) : (issueSystem (F := F) t ctxIss).length = 4008 := by
  simp [issueSystem, bitSystem, issueOutput, issueKeccak, qsKeccak_length, issueWitnessBits]

/-- The constraint values computed with sharing (`qsKeccakValues`), for the differential test. -/
def issueValues [Add F] [Mul F] [Zero F] [One F] (t : Fin M → UInt8) (ctxIss : ℕ → UInt8)
    (w : ℕ → F) : List F :=
  let kv := qsKeccakValues w issueOffStates 360 (by norm_num)
    ((qsInput (F := F) (issuePub ctxIss) issueMap).map (Expr.eval w))
  (bitSystem issueWitnessBits).values w ++ kv.1 ++
    (List.finRange 360).map fun i => kv.2[i] + bitF (tBit t i)

theorem issueValues_eq [Add F] [Mul F] [Zero F] [One F] (t : Fin M → UInt8) (ctxIss : ℕ → UInt8)
    (w : ℕ → F) : issueValues t ctxIss w = (issueSystem t ctxIss).values w := by
  obtain ⟨h1, h2⟩ := qsKeccak_values w issueOffStates 360 (by norm_num)
    (qsInput (F := F) (issuePub ctxIss) issueMap)
  unfold issueValues issueSystem issueKeccak
  dsimp only
  rw [System.values] at h1
  rw [System.values, System.values, List.map_append, List.map_append, h1, issueOutput,
    List.map_map]
  rw [List.append_cancel_left_eq]
  refine List.map_congr_left fun i _ => ?_
  have := congrArg (fun v => v[i]) h2
  simp only [Vector.getElem_map, Fin.getElem_fin] at this
  simp only [Function.comp, Expr.eval_add, Expr.eval_const, Fin.getElem_fin, this]

/-- The issue relation: `t = Com(nf, ctx_iss, ctx_red, r)`. -/
def issueRel (t : Fin M → UInt8) (ctxIss nf ctxRed r : ℕ → UInt8) : Prop :=
  t = com nf ctxIss ctxRed r

variable [Field F] [CharP F 2]

theorem bitSystem_holds (B : ℕ) (w : ℕ → Bool) : (bitSystem B).Holds (ofBits w : ℕ → F) := by
  intro e he
  obtain ⟨n, -, rfl⟩ := List.mem_map.1 he
  exact bitConstraint_bits w _

theorem bitSystem_sound [DecidableEq F] {B : ℕ} {w : ℕ → F} (h : (bitSystem B).Holds w) :
    ∀ i < B, w i = bitF (decide (w i = 1)) := fun i hi =>
  eq_bitF_of_bitConstraint (h _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))

theorem eval_qsInput_congr (pub : State) (map : Fin 100 → Option ℕ) (B : ℕ)
    (hmap : ∀ k b, map k = some b → b < B / 8) (w : ℕ → F) (wb : ℕ → Bool)
    (hw : ∀ i < B, w i = bitF (wb i)) (i : ℕ) (hi : i < 800) :
    (qsInput (F := F) pub map)[i].eval w = (qsInput (F := F) pub map)[i].eval (ofBits wb) := by
  simp only [qsInput, Vector.getElem_ofFn]
  split
  · next b hb =>
    have := hmap _ _ hb
    have : i % 8 < 8 := Nat.mod_lt _ (by norm_num)
    simp only [Expr.eval_wit, ofBits]
    exact hw _ (by omega)
  · rfl

theorem issueMap_lt : ∀ k b, issueMap k = some b → b < issueWitnessBits / 8 := by
  intro k b h
  simp only [issueMap, issueOffR, issueOffCtxRed, issueOffNf] at h
  split_ifs at h <;> simp only [Option.some.injEq] at h <;> simp only [issueWitnessBits] <;> omega

/-- **Completeness.** A bit vector with arbitrary `r`, `ctx_red`, `nf`, honest committed states
(`encode_committed_states`, `segmented.hpp:113-119`) and `t = Com(nf, ctx_iss, ctx_red, r)`
satisfies every constraint. -/
theorem issue_complete (t : Fin M → UInt8) (ctxIss : ℕ → UInt8) (w : ℕ → Bool)
    (h5 : ∀ i < 800, w (8 * issueOffStates + i) =
      stateBit (keccakP800Rounds 0 5 (encodeComState (issueNf w) ctxIss (issueCtxRed w) (issueR w))) i)
    (h9 : ∀ i < 800, w (8 * (issueOffStates + 100) + i) =
      stateBit (keccakP800Rounds 0 9 (encodeComState (issueNf w) ctxIss (issueCtxRed w) (issueR w))) i)
    (hrel : issueRel t ctxIss (issueNf w) (issueCtxRed w) (issueR w)) :
    (issueSystem t ctxIss).Holds (ofBits w : ℕ → F) := by
  rw [← inputState_issue] at h5 h9
  have hK := qsKeccak_complete (F := F) (issuePub ctxIss) issueMap w issueOffStates 360
    (by norm_num) h5 h9
  rw [issueSystem, System.holds_append, System.holds_append]
  refine ⟨⟨bitSystem_holds _ w, hK⟩, ?_⟩
  intro e he
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
  have hi := i.isLt
  rw [Expr.eval_add, Expr.eval_const, issueKeccak, Fin.getElem_fin,
    qsKeccak_sound (issuePub ctxIss) issueMap w _ 360 _ hK i.val hi]
  have hb : stateBit (keccakP800 (inputState (issuePub ctxIss) issueMap w)) i.val = tBit t i := by
    rw [stateBit_eq _ _ (by omega), tBit, hrel, com, inputState_issue]
  rw [hb]; exact CharTwo.add_self_eq_zero _

/-- **Soundness.** If the constraints hold at any committed values `w ∈ F^ℓ`, all 2048 witness
bits are bits, and their decoding satisfies `t = Com(nf, ctx_iss, ctx_red, r)`. -/
theorem issue_sound [DecidableEq F] (t : Fin M → UInt8) (ctxIss : ℕ → UInt8) (w : ℕ → F)
    (hw : (issueSystem t ctxIss).Holds w) :
    (∀ i < issueWitnessBits, w i = bitF (decide (w i = 1))) ∧
      issueRel t ctxIss (issueNf fun i => decide (w i = 1))
        (issueCtxRed fun i => decide (w i = 1)) (issueR fun i => decide (w i = 1)) := by
  set wb : ℕ → Bool := fun i => decide (w i = 1)
  rw [issueSystem, System.holds_append, System.holds_append] at hw
  obtain ⟨⟨hb, hK⟩, hout⟩ := hw
  have hbit := bitSystem_sound hb
  refine ⟨hbit, ?_⟩
  obtain ⟨hc1, hc2⟩ := qsKeccak_congr w (ofBits wb) issueOffStates 360 (by norm_num)
    (qsInput (F := F) (issuePub ctxIss) issueMap)
    (eval_qsInput_congr _ _ _ issueMap_lt w wb hbit)
    (fun i hi => hbit _ (by simp only [issueOffStates, issueWitnessBits]; omega))
  have hK' := (holds_congr hc1).1 hK
  unfold issueRel
  funext k
  rw [com, ← inputState_issue]
  refine UInt8.eq_of_byteBit fun j hj => ?_
  have hk : k.val < 45 := k.isLt
  have hi : 8 * k.val + j < 360 := by omega
  have ho := hout _ (List.mem_map.2 ⟨⟨8 * k.val + j, hi⟩, List.mem_finRange _, rfl⟩)
  simp only [Expr.eval_add, Expr.eval_const] at ho
  have ho' := (CharTwo.add_eq_zero (R := F)).1 ho
  rw [issueKeccak, Fin.getElem_fin, hc2 _ hi, qsKeccak_sound _ _ wb _ _ _ hK' _ hi,
    stateBit_eight _ _ _ (by omega) hj] at ho'
  have := bitF_injective ho'
  rw [this, tBit]
  have e1 : (8 * k.val + j) / 8 = k.val := by omega
  have e2 : (8 * k.val + j) % 8 = j := by omega
  simp only [e1, e2]

end Issue

/-! ## Redeem (`src/moussaka/redeem.hpp`) -/

section Redeem

/-- `REDEEM_WIT_OFF_R`, `_S`, `_STATES`, `_B` (`redeem.hpp:74-77`). -/
def redeemOffR : ℕ := 0
def redeemOffS : ℕ := 16
def redeemOffStates : ℕ := 135
def redeemOffB : ℕ := 335

/-- `REDEEM_WITNESS_BITS = 8 · 343` (`redeem.hpp:79-81`). -/
def redeemWitnessBits : ℕ := 8 * 343

/-- `selector_bit(u) = 8 · REDEEM_WIT_OFF_B + u` (`redeem.hpp:84`). -/
def selBit (u : ℕ) : ℕ := 8 * redeemOffB + u

/-- `REDEEM_COM_TO_WIT` (`redeem.hpp:88-95`): only the opening is secret. -/
def redeemMap : Fin 100 → Option ℕ := fun k =>
  if 7 ≤ k.val ∧ k.val < 23 then some (redeemOffR + (k.val - 7)) else none

/-- `encode_com_state(x.nf, x.ctx_iss, x.ctx_red, {})` (`redeem.hpp:247`). -/
def redeemPub (nf ctxIss ctxRed : ℕ → UInt8) : State := encodeComState nf ctxIss ctxRed fun _ => 0

/-- The decoded opening `r`. -/
def redeemR (w : ℕ → Bool) : ℕ → UInt8 := fun i => witByte w (redeemOffR + i)

/-- **Input wiring** (`L7-keccak.md` §4.2, test `KeccakInputIsCommitmentInput`). -/
theorem inputState_redeem (nf ctxIss ctxRed : ℕ → UInt8) (w : ℕ → Bool) :
    inputState (redeemPub nf ctxIss ctxRed) redeemMap w =
      encodeComState nf ctxIss ctxRed (redeemR w) := by
  apply Vector.ext
  intro k hk
  simp only [inputState, Vector.getElem_ofFn]
  unfold redeemMap
  simp only [redeemPub, encodeComState, Vector.getElem_ofFn, redeemR, redeemOffR]
  by_cases a1 : k < 7
  · simp [a1, show ¬ 7 ≤ k by omega]
  by_cases a2 : k < 23
  · simp [a1, a2, show 7 ≤ k by omega]
  · simp [a1, a2]

variable {F K : Type*}

/-- `prefix` after `u` steps: `b[0] + b[1] + ⋯ + b[u]` (`redeem.hpp:235-239`). -/
def prefixE [Add F] : ℕ → Expr F
  | 0 => Expr.wit (selBit 0)
  | u + 1 => prefixE u + Expr.wit (selBit (u + 1))

/-- The selector constraints (`redeem.hpp:222-242`) for an Anchor Set of size `n`: `b[u]` is a bit
for `u < n` and zero otherwise (`u < MAX_ANCHORS = 64`), the parity constraints
`prefix_u · b[u+1]`, `u < 63`, and the weight constraint `prefix_63 + 1`. -/
def selectorSystem [Add F] [Mul F] [One F] (n : ℕ) : System F :=
  (List.range 64).map (fun u =>
      if u < n then bitConstraint (Expr.wit (selBit u)) else Expr.wit (selBit u)) ++
    (List.range 63).map (fun u => prefixE u * Expr.wit (selBit (u + 1))) ++
    [prefixE 63 + Expr.const 1]

/-- The Keccak part: `qs_keccak(qs_input(…), REDEEM_WIT_OFF_STATES)`, all 800 output bits
(`redeem.hpp:245-249`). -/
def redeemKeccak [Zero F] [One F] (nf ctxIss ctxRed : ℕ → UInt8) :
    System F × Vector (Expr F) 800 :=
  qsKeccak redeemOffStates 800 le_rfl (qsInput (redeemPub nf ctxIss ctxRed) redeemMap)

/-- `lq = 0; lq += b[u] · qs_eval_combined_public_map(anchors[u], s, l)` for `u < n`
(`redeem.hpp:250-262`), with `s_i = load_witness_8_bits_and_combine(8 (REDEEM_WIT_OFF_S + i))`. -/
def lqExpr [Add F] [Mul F] [Zero F] [One F] (β : Fin 8 → F) (toBits : K → Fin 8 → Bool)
    (anchors : List (ℕ → K)) (l : Fin M → F) : Expr F :=
  (List.finRange anchors.length).foldl (fun acc (u : Fin anchors.length) => acc + Expr.wit (selBit u) *
    evalCombinedPublicMap β toBits N M anchors[u] (fun i => byteLoad β (redeemOffS + i)) l)
    (Expr.const 0)

/-- `lout = 0; lout += l.coeff(k) · qs_byte(out, k)` for `k < M` (`redeem.hpp:266-269`). -/
def loutExpr [Add F] [Mul F] [Zero F] (β : Fin 8 → F) (l : Fin M → F) (out : Vector (Expr F) 800) :
    Expr F :=
  linComb l fun k => qsByte β out k.val (by have : k.val < 45 := k.isLt; omega)

/-- The output constraint `lout + qs_lift(lq)` (`redeem.hpp:270`). -/
def redeemOutput [Add F] [Mul F] [Zero F] [One F] (β : Fin 8 → F) (toBits : K → Fin 8 → Bool)
    (anchors : List (ℕ → K)) (l : Fin M → F) (out : Vector (Expr F) 800) : Expr F :=
  loutExpr β l out + lqExpr β toBits anchors l

/-- `RedeemRelation::constraints(qs, {anchors, nf, ctx_iss, ctx_red, _}, chal2)`
(`redeem.hpp:202-271`). `anchors k` is the expanded key `PublicKeyAccess::expanded(anchors[k])`;
`l = Combination(chal2, MOUSSAKA_REDEEM_COMBINE_DST)`. -/
def redeemSystem [Add F] [Mul F] [Zero F] [One F] (β : Fin 8 → F) (toBits : K → Fin 8 → Bool)
    (anchors : List (ℕ → K)) (nf ctxIss ctxRed : ℕ → UInt8) (l : Fin M → F) : System F :=
  bitSystem (8 * redeemOffB) ++ selectorSystem anchors.length ++
    (redeemKeccak nf ctxIss ctxRed).1 ++
    [redeemOutput β toBits anchors l (redeemKeccak nf ctxIss ctxRed).2]

theorem redeemSystem_length [Add F] [Mul F] [Zero F] [One F] (β : Fin 8 → F)
    (toBits : K → Fin 8 → Bool) (anchors : List (ℕ → K)) (nf ctxIss ctxRed : ℕ → UInt8)
    (l : Fin M → F) : (redeemSystem β toBits anchors nf ctxIss ctxRed l).length = 4409 := by
  simp [redeemSystem, bitSystem, selectorSystem, redeemKeccak, qsKeccak_length, redeemOffB]

theorem eval_linComb_congr [Add F] [Mul F] [Zero F] {n : ℕ} (l : Fin n → F) (T T' : Fin n → Expr F)
    (w w' : ℕ → F) (h : ∀ k, (T k).eval w = (T' k).eval w') :
    (linComb l T).eval w = (linComb l T').eval w' := by
  have : ∀ (L : List (Fin n)) (a a' : Expr F), a.eval w = a'.eval w' →
      (L.foldl (fun acc k => acc + Expr.const (l k) * T k) a).eval w =
        (L.foldl (fun acc k => acc + Expr.const (l k) * T' k) a').eval w' := by
    intro L
    induction L with
    | nil => exact fun _ _ h => h
    | cons k L ih =>
      intro a a' ha
      exact ih _ _ (by simp only [Expr.eval_add, Expr.eval_mul, Expr.eval_const, ha, h k])
  exact this _ _ _ rfl

theorem eval_loutExpr_congr [Add F] [Mul F] [Zero F] (β : Fin 8 → F) (l : Fin M → F)
    (out out' : Vector (Expr F) 800) (w w' : ℕ → F)
    (h : ∀ i (hi : i < 800), out[i].eval w = out'[i].eval w') :
    (loutExpr β l out).eval w = (loutExpr β l out').eval w' := by
  refine eval_linComb_congr l _ _ w w' fun k => ?_
  have : k.val < 45 := k.isLt
  simp only [qsByte, Expr.eval_add, Expr.eval_mul, Expr.eval_const]
  rw [h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega),
    h _ (by omega), h _ (by omega), h _ (by omega)]

/-- The constraint values computed with sharing (`qsKeccakValues`), for the differential test. -/
def redeemValues [Add F] [Mul F] [Zero F] [One F] (β : Fin 8 → F) (toBits : K → Fin 8 → Bool)
    (anchors : List (ℕ → K)) (nf ctxIss ctxRed : ℕ → UInt8) (l : Fin M → F) (w : ℕ → F) :
    List F :=
  let kv := qsKeccakValues w redeemOffStates 800 le_rfl
    ((qsInput (F := F) (redeemPub nf ctxIss ctxRed) redeemMap).map (Expr.eval w))
  (bitSystem (8 * redeemOffB) ++ selectorSystem anchors.length).values w ++ kv.1 ++
    [(redeemOutput β toBits anchors l (kv.2.map Expr.const)).eval w]

theorem redeemValues_eq [Add F] [Mul F] [Zero F] [One F] (β : Fin 8 → F)
    (toBits : K → Fin 8 → Bool) (anchors : List (ℕ → K)) (nf ctxIss ctxRed : ℕ → UInt8)
    (l : Fin M → F) (w : ℕ → F) :
    redeemValues β toBits anchors nf ctxIss ctxRed l w =
      (redeemSystem β toBits anchors nf ctxIss ctxRed l).values w := by
  obtain ⟨h1, h2⟩ := qsKeccak_values w redeemOffStates 800 le_rfl
    (qsInput (F := F) (redeemPub nf ctxIss ctxRed) redeemMap)
  unfold redeemValues redeemSystem redeemKeccak
  dsimp only
  rw [System.values] at h1
  simp only [System.values, List.map_append, List.map_singleton, h1, List.append_cancel_left_eq,
    List.cons.injEq, and_true]
  simp only [redeemOutput, Expr.eval_add]
  rw [eval_loutExpr_congr β l _ _ w w fun i hi => ?_]
  have := congrArg (fun v => v[i]) h2
  simp only [Vector.getElem_map] at this
  simp [this]

/-- GF(256) element of a byte (bit `j` of the byte is bit `j` of the element). -/
def toK (ofByte : (Fin 8 → Bool) → K) (x : UInt8) : K := ofByte fun j => byteBit x j

/-- The UOV target of the redeem relation: `Com(nf, ctx_iss, ctx_red, r)` as GF(256) elements. -/
def redeemTarget (ofByte : (Fin 8 → Bool) → K) (nf ctxIss ctxRed r : ℕ → UInt8) : Fin M → K :=
  fun k => toK ofByte (com nf ctxIss ctxRed r k)

/-- The decoded preimage `σ`. -/
def redeemS (ofByte : (Fin 8 → Bool) → K) (w : ℕ → Bool) : ℕ → K := decode ofByte w redeemOffS

/-- The redeem relation (`security/moussaka.md` §1, "Redemption"): the selected Anchor's public
map sends `σ` to the commitment `Com(nf, ctx_iss, ctx_red, r)`, in all 45 components. -/
def redeemRel [Add K] [Mul K] [Zero K] (ofByte : (Fin 8 → Bool) → K) (anchors : List (ℕ → K))
    (nf ctxIss ctxRed r : ℕ → UInt8) (σ : ℕ → K) (u₀ : ℕ) : Prop :=
  ∃ h : u₀ < anchors.length, publicMap N M anchors[u₀] σ = redeemTarget ofByte nf ctxIss ctxRed r

variable [Field F] [CharP F 2] [Add K] [Mul K] [Zero K]
variable {β : Fin 8 → F} {toBits : K → Fin 8 → Bool} {ofByte : (Fin 8 → Bool) → K}

theorem eval_prefixE (w : ℕ → F) (u : ℕ) :
    (prefixE u).eval w = VoleMole.Moussaka.pre (fun k => w (selBit k)) u := by
  induction u with
  | zero => simp [prefixE, VoleMole.Moussaka.pre]
  | succ u ih => rw [VoleMole.Moussaka.pre_succ, ← ih]; rfl

theorem embed_toK (hι : IsEmbedding β toBits ofByte) (x : UInt8) :
    embed β (toBits (toK ofByte x)) = ∑ j : Fin 8, β j * bitF (byteBit x j) := by
  rw [toK, hι.toBits_ofByte, embed_eq]

/-- The output constraint's value, given bits on `s`, a one-hot selector at `u₀`, and Keccak
outputs equal to the bits of `keccak_p800(encode_com_state(nf, ctx_iss, ctx_red, r))`. -/
theorem eval_redeemOutput (hι : IsEmbedding β toBits ofByte) (hβ : β 0 = 1)
    (anchors : List (ℕ → K)) (nf ctxIss ctxRed : ℕ → UInt8) (l : Fin M → F)
    (out : Vector (Expr F) 800) (w : ℕ → F) (wb : ℕ → Bool)
    (hs : ∀ n < 8 * N, w (8 * redeemOffS + n) = bitF (wb (8 * redeemOffS + n)))
    (u₀ : ℕ) (hu₀ : u₀ < anchors.length)
    (hsel : ∀ u < anchors.length, w (selBit u) = if u = u₀ then 1 else 0)
    (hout : ∀ i (hi : i < 800), out[i].eval w =
      bitF (stateBit (keccakP800 (encodeComState nf ctxIss ctxRed (redeemR wb))) i)) :
    (redeemOutput β toBits anchors l out).eval w =
      ∑ k, l k * (embed β (toBits (publicMap N M anchors[u₀] (redeemS ofByte wb) k)) +
        embed β (toBits (redeemTarget ofByte nf ctxIss ctxRed (redeemR wb) k))) := by
  have hlout : (loutExpr β l out).eval w =
      ∑ k, l k * embed β (toBits (redeemTarget ofByte nf ctxIss ctxRed (redeemR wb) k)) := by
    rw [loutExpr, eval_linComb]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk : k.val < 45 := k.isLt
    congr 1
    rw [redeemTarget, embed_toK hι, com]
    set X := keccakP800 (encodeComState nf ctxIss ctxRed (redeemR wb))
    have e : ∀ j < 8, stateBit X (8 * k.val + j) = byteBit X[k.val] j := fun j hj =>
      stateBit_eight X k.val j (by omega) hj
    have e0 : stateBit X (8 * k.val) = byteBit X[k.val] 0 := e 0 (by norm_num)
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
  have hlq : (lqExpr β toBits anchors l).eval w =
      ∑ k, l k * embed β (toBits (publicMap N M anchors[u₀] (redeemS ofByte wb) k)) := by
    rw [lqExpr, eval_foldl_add, Expr.eval_const, zero_add, ← Fin.sum_univ_def,
      Finset.sum_eq_single ⟨u₀, hu₀⟩]
    · simp only [Expr.eval_mul, Expr.eval_wit, hsel u₀ hu₀, ite_true, one_mul]
      exact eval_evalCombinedPublicMap_of_bits hι N M anchors[u₀] l _ w wb hs
    · intro u _ hu
      have : u.val ≠ u₀ := fun h => hu (Fin.ext h)
      simp only [Expr.eval_mul, Expr.eval_wit, hsel u.val u.isLt, this, ite_false, zero_mul]
    · exact fun h => absurd (Finset.mem_univ _) h
  rw [redeemOutput, Expr.eval_add, hlout, hlq, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem mem_selector_bit (n u : ℕ) (hu : u < 64) :
    (if u < n then bitConstraint (Expr.wit (selBit u)) else Expr.wit (selBit u)) ∈
      (selectorSystem n : System F) :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_map.2 ⟨u, List.mem_range.2 hu, rfl⟩))

theorem mem_selector_parity (n u : ℕ) (hu : u < 63) :
    prefixE u * Expr.wit (selBit (u + 1)) ∈ (selectorSystem n : System F) :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨u, List.mem_range.2 hu, rfl⟩))

theorem mem_selector_weight (n : ℕ) :
    prefixE 63 + Expr.const 1 ∈ (selectorSystem n : System F) :=
  List.mem_append_right _ (List.mem_singleton_self _)

/-- **Selector soundness** (`L7-uov.md` Lemma 4, over any committed values): the selector
constraints force every `b[u]` to be a bit and `b = e_{u₀}` for a unique `u₀ < n`. (The parity
and weight part is `VoleMole.Moussaka.selector_one_hot`.) -/
theorem selector_sound [DecidableEq F] (n : ℕ) (w : ℕ → F) (h : (selectorSystem n).Holds w) :
    (∀ u < 64, w (selBit u) = bitF (decide (w (selBit u) = 1))) ∧
      ∃ u₀ < n, ∀ u < 64, w (selBit u) = if u = u₀ then 1 else 0 := by
  have hzero : ∀ u < 64, n ≤ u → w (selBit u) = 0 := fun u hu hnu => by
    have := h _ (mem_selector_bit n u hu)
    simpa only [show ¬ u < n by omega, ↓reduceIte, Expr.eval_wit] using this
  have hbit : ∀ u < 64, w (selBit u) = bitF (decide (w (selBit u) = 1)) := by
    intro u hu
    by_cases hnu : u < n
    · have := h _ (mem_selector_bit n u hu)
      simp only [hnu, ↓reduceIte] at this
      exact eq_bitF_of_bitConstraint this
    · rw [hzero u hu (by omega)]; simp [bitF]
  refine ⟨hbit, ?_⟩
  set b : ℕ → F := fun u => w (selBit u)
  have hpar : ∀ u, u + 1 < 64 → VoleMole.Moussaka.pre b u * b (u + 1) = 0 := fun u hu => by
    have := h _ (mem_selector_parity n u (by omega))
    rwa [Expr.eval_mul, eval_prefixE] at this
  have hsum : ∑ k ∈ range 64, b k = 1 := by
    have := h _ (mem_selector_weight n)
    rw [Expr.eval_add, eval_prefixE, Expr.eval_const] at this
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

/-- **Selector completeness**: a one-hot `b = e_{u₀}`, `u₀ < n`, satisfies the selector
constraints. -/
theorem selector_complete (n : ℕ) (w : ℕ → Bool) (u₀ : ℕ) (hu₀ : u₀ < n) (hn : n ≤ 64)
    (hsel : ∀ u < 64, w (selBit u) = decide (u = u₀)) :
    (selectorSystem n).Holds (ofBits w : ℕ → F) := by
  have hpre : ∀ u < 64, (prefixE u).eval (ofBits w : ℕ → F) = if u₀ ≤ u then 1 else 0 := by
    intro u
    induction u with
    | zero =>
      intro _
      simp only [prefixE, Expr.eval_wit, ofBits, hsel 0 (by norm_num), bitF]
      by_cases h0 : u₀ = 0 <;> simp [h0, eq_comm]
    | succ u ih =>
      intro hu
      simp only [prefixE, Expr.eval_add, Expr.eval_wit, ofBits, hsel (u + 1) hu, bitF,
        ih (by omega)]
      by_cases h1 : u₀ ≤ u
      · simp [h1, show u₀ ≤ u + 1 by omega, show u + 1 ≠ u₀ by omega]
      · by_cases h2 : u₀ = u + 1
        · simp [h2]
        · simp [h1, show ¬ u₀ ≤ u + 1 by omega, Ne.symm h2]
  intro e he
  simp only [selectorSystem, List.mem_append, List.mem_map, List.mem_range,
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

theorem redeemMap_lt : ∀ k b, redeemMap k = some b → b < 8 * redeemOffB / 8 := by
  intro k b h
  simp only [redeemMap, redeemOffR] at h
  split_ifs at h
  simp only [Option.some.injEq] at h
  simp only [redeemOffB]; omega

/-- **Completeness.** A bit vector with arbitrary `r`, `s`, honest committed states, a one-hot
selector `b = e_{u₀}` (`u₀ < n ≤ 64`) and `P_{anchors[u₀]}(σ) = Com(nf, ctx_iss, ctx_red, r)`
satisfies every constraint, for every `l`. -/
theorem redeem_complete (hι : IsEmbedding β toBits ofByte) (hβ : β 0 = 1)
    (anchors : List (ℕ → K)) (hn : anchors.length ≤ 64) (nf ctxIss ctxRed : ℕ → UInt8)
    (l : Fin M → F) (w : ℕ → Bool)
    (h5 : ∀ i < 800, w (8 * redeemOffStates + i) =
      stateBit (keccakP800Rounds 0 5 (encodeComState nf ctxIss ctxRed (redeemR w))) i)
    (h9 : ∀ i < 800, w (8 * (redeemOffStates + 100) + i) =
      stateBit (keccakP800Rounds 0 9 (encodeComState nf ctxIss ctxRed (redeemR w))) i)
    (u₀ : ℕ) (hsel : ∀ u < 64, w (selBit u) = decide (u = u₀))
    (hrel : redeemRel ofByte anchors nf ctxIss ctxRed (redeemR w) (redeemS ofByte w) u₀) :
    (redeemSystem β toBits anchors nf ctxIss ctxRed l).Holds (ofBits w) := by
  obtain ⟨hu₀, hP⟩ := hrel
  rw [← inputState_redeem] at h5 h9
  have hK := qsKeccak_complete (F := F) (redeemPub nf ctxIss ctxRed) redeemMap w redeemOffStates
    800 le_rfl h5 h9
  rw [redeemSystem, System.holds_append, System.holds_append, System.holds_append]
  refine ⟨⟨⟨bitSystem_holds _ w, selector_complete _ w u₀ hu₀ hn hsel⟩, hK⟩, ?_⟩
  intro e he
  rw [List.mem_singleton] at he
  subst he
  rw [eval_redeemOutput hι hβ anchors nf ctxIss ctxRed l _ (ofBits w) w (fun _ _ => rfl) u₀ hu₀
    (fun u hu => by simp [ofBits, hsel u (by omega), bitF])
    (fun i hi => by
      rw [redeemKeccak, qsKeccak_sound _ _ w _ _ _ hK i hi, inputState_redeem]), hP]
  simp [CharTwo.add_self_eq_zero]

/-- **Soundness (deterministic).** If the constraints hold at any committed values `w ∈ F^ℓ` and
`n ≤ MAX_ANCHORS`, then every witness bit is a bit, the selector is `e_{u₀}` for some `u₀ < n`,
and the decoded `(r, σ)` satisfy the combined equation
`Σ_k l_k (ι(P_{u₀}(σ)_k) + ι(Com(nf, ctx_iss, ctx_red, r)_k)) = 0`. -/
theorem redeem_sound [DecidableEq F] (hι : IsEmbedding β toBits ofByte) (hβ : β 0 = 1)
    (anchors : List (ℕ → K)) (hn : anchors.length ≤ 64) (nf ctxIss ctxRed : ℕ → UInt8)
    (l : Fin M → F) (w : ℕ → F) (hw : (redeemSystem β toBits anchors nf ctxIss ctxRed l).Holds w) :
    (∀ i < redeemWitnessBits, w i = bitF (decide (w i = 1))) ∧
      ∃ u₀, ∃ hu₀ : u₀ < anchors.length,
        (∀ u < 64, decide (w (selBit u) = 1) = decide (u = u₀)) ∧
        ∑ k, l k * (embed β (toBits (publicMap N M anchors[u₀]
            (redeemS ofByte fun i => decide (w i = 1)) k)) +
          embed β (toBits (redeemTarget ofByte nf ctxIss ctxRed
            (redeemR fun i => decide (w i = 1)) k))) = 0 := by
  set wb : ℕ → Bool := fun i => decide (w i = 1)
  rw [redeemSystem, System.holds_append, System.holds_append, System.holds_append] at hw
  obtain ⟨⟨⟨hb, hs⟩, hK⟩, hout⟩ := hw
  have hbit1 := bitSystem_sound hb
  obtain ⟨hbit2, u₀, hu₀, hsel⟩ := selector_sound _ w hs
  have hbit : ∀ i < redeemWitnessBits, w i = bitF (wb i) := by
    intro i hi
    by_cases h : i < 8 * redeemOffB
    · exact hbit1 i h
    · have := hbit2 (i - 8 * redeemOffB) (by simp only [redeemWitnessBits, redeemOffB] at *; omega)
      rwa [selBit, show 8 * redeemOffB + (i - 8 * redeemOffB) = i by omega] at this
  have hsel' : ∀ u < 64, wb (selBit u) = decide (u = u₀) := fun u hu => by
    simp only [wb, hsel u hu]
    split_ifs with h <;> simp [h]
  refine ⟨hbit, u₀, by omega, hsel', ?_⟩
  obtain ⟨hc1, hc2⟩ := qsKeccak_congr w (ofBits wb) redeemOffStates 800 le_rfl
    (qsInput (F := F) (redeemPub nf ctxIss ctxRed) redeemMap)
    (eval_qsInput_congr _ _ _ redeemMap_lt w wb hbit1)
    (fun i hi => hbit1 _ (by simp only [redeemOffStates, redeemOffB]; omega))
  have hK' := (holds_congr hc1).1 hK
  have := hout _ (List.mem_singleton_self _)
  rwa [eval_redeemOutput hι hβ anchors nf ctxIss ctxRed l _ w wb
    (fun n hn => hbit _ (by simp only [redeemOffS, redeemWitnessBits, N] at *; omega)) u₀
    (by omega) (fun u hu => hsel u (by omega))
    (fun i hi => by
      rw [redeemKeccak, hc2 i hi, qsKeccak_sound _ _ wb _ _ _ hK' i hi, inputState_redeem])] at this

/-- **The combination step.** If `σ` is not a preimage of the commitment under `anchors[u₀]`,
exactly a `1/|F|` fraction of the coefficient vectors `l` passes the combined equation. -/
theorem redeem_card_bad [Fintype F] [DecidableEq F] (hι : IsEmbedding β toBits ofByte)
    {anchors : List (ℕ → K)} {nf ctxIss ctxRed r : ℕ → UInt8} {σ : ℕ → K} {u₀ : ℕ}
    (hu₀ : u₀ < anchors.length)
    (hrel : publicMap N M anchors[u₀] σ ≠ redeemTarget ofByte nf ctxIss ctxRed r) :
    #{l : Fin M → F | ∑ k, l k * (embed β (toBits (publicMap N M anchors[u₀] σ k)) +
      embed β (toBits (redeemTarget ofByte nf ctxIss ctxRed r k))) = 0} * Fintype.card F =
      Fintype.card (Fin M → F) :=
  uov_card_bad hι hrel

open Classical in
/-- **Soundness, end to end.** Fix the committed values `w ∈ F^ℓ` and the instance before drawing
`l`, with `n ≤ MAX_ANCHORS`. Either `w` is a bit vector on all `8·343` witness bits whose selector
is `e_{u₀}` with `u₀ < n` and whose `(r, σ)` satisfy `P_{anchors[u₀]}(σ) = Com(nf, ctx_iss,
ctx_red, r)`, or at most a `1/|F|` fraction of the `l` make every constraint hold. -/
theorem redeem_sound_card [Fintype F] [DecidableEq F] (hι : IsEmbedding β toBits ofByte)
    (hβ : β 0 = 1) (anchors : List (ℕ → K)) (hn : anchors.length ≤ 64)
    (nf ctxIss ctxRed : ℕ → UInt8) (w : ℕ → F) :
    (∃ wb : ℕ → Bool, (∀ i < redeemWitnessBits, w i = bitF (wb i)) ∧
        ∃ u₀, (∀ u < 64, wb (selBit u) = decide (u = u₀)) ∧
          redeemRel ofByte anchors nf ctxIss ctxRed (redeemR wb) (redeemS ofByte wb) u₀) ∨
      #{l : Fin M → F | (redeemSystem β toBits anchors nf ctxIss ctxRed l).Holds w} *
        Fintype.card F ≤ Fintype.card (Fin M → F) := by
  set wb : ℕ → Bool := fun i => decide (w i = 1)
  by_cases hS : #{l : Fin M → F | (redeemSystem β toBits anchors nf ctxIss ctxRed l).Holds w} = 0
  · right; rw [hS, zero_mul]; exact Nat.zero_le _
  obtain ⟨l₀, hl₀⟩ := Finset.card_ne_zero.1 hS
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl₀
  obtain ⟨hbit, u₀, hu₀, hsel, -⟩ := redeem_sound hι hβ anchors hn nf ctxIss ctxRed l₀ w hl₀
  by_cases hP : publicMap N M anchors[u₀] (redeemS ofByte wb) =
      redeemTarget ofByte nf ctxIss ctxRed (redeemR wb)
  · exact Or.inl ⟨wb, hbit, u₀, hsel, hu₀, hP⟩
  right
  rw [← redeem_card_bad hι hu₀ hP]
  refine Nat.mul_le_mul_right _ (Finset.card_le_card fun l hl => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
  obtain ⟨-, u₁, hu₁, hsel₁, hcomb⟩ := redeem_sound hι hβ anchors hn nf ctxIss ctxRed l w hl
  have : u₁ = u₀ := by
    have h1 := hsel₁ u₀ (by omega)
    rw [hsel u₀ (by omega)] at h1
    simpa [eq_comm] using h1
  subst this
  exact hcomb

end Redeem

end VoleMole.Arith.Moussaka
