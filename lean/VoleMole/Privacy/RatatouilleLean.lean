import VoleMole.Privacy.MoussakaLean

/-!
# Ratatouille with the Lean prover, assembled per relation

`Privacy.Ratatouille.unlinkability_lean` (`Privacy/LeanProver.lean`) takes the primitives, the
statement builders, the witness encodings, the encodings of the proofs into the spec's proof types
and their deterministic hypotheses as parameters. Here they are built and proved for the
label-row layout (`Spec.Ratatouille.Sizes.labelRows`: proofs of 7256 and 17575 bytes):

* `stI x`: `Verifier.ratatouilleIssue` with label rows; `stS x`: `Verifier.ratatouilleSpend` for the
  spec's key (its public map; the spec's key has no digest, so the instance encoding has the other
  fields only), with label rows. `encI`, `encS`: the spec's witness encodings
  (`encodeIssueWitness`, `encodeSpendWitness`, checked against the C++ by `spec_kats`).
* `leanPrim`: the primitives whose provers and verifiers are the Lean prover and verifier, the
  proofs as the spec's fixed-size vectors (`vecOf`).
* `issue_holds`, `spend_holds`: the encodings satisfy the systems for every combination (from
  `Arith.Ratatouille.issue_complete` and `spend_complete_gf128`: the committed Keccak states, the
  carries of the two additions (`carries_testBit`) and the relation).
* **`unlinkability_label_rows`**: Theorem 2 with the Lean prover, `≤ 4εI + 4εS + 2εhide`, assuming
  only the tape hypotheses (`TapeHyp`), hiding and `HashesWF` (BAVC and CRT completeness are
  theorems, `Bridge.bavcComplete`, `Bridge.crtComplete`); `unlinkability_label_rows_shake` drops
  `HashesWF` for SHAKE.
-/

open Finset

namespace VoleMole.Privacy.Ratatouille

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.ZK.Sim VoleMole.Arith
open VoleMole.EndToEnd VoleMole.Spec.Ratatouille

/-! ## The carries of an addition -/

/-- The carries of `a + b`: `c₀ = 0`, `c_{j+1} = maj(a_j, b_j, c_j)`. -/
def cc (a b : UInt64) : ℕ → Bool
  | 0 => false
  | j + 1 => Arith.Ratatouille.maj (a.toNat.testBit j) (b.toNat.testBit j) (cc a b j)

lemma bit_and_one (a : UInt64) {i : ℕ} (hi : i < 64) :
    (a >>> i.toUInt64 &&& 1) = bif a.toNat.testBit i then 1 else 0 := by
  apply UInt64.toNat_inj.1
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight, Nat.testBit_eq_decide_div_mod_eq]
  have hi' : i.toUInt64.toNat % 64 = i := by
    rw [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt hi]
  rw [hi', Nat.shiftRight_eq_div_pow, show (1 : UInt64).toNat = 1 from rfl, Nat.and_one_is_mod]
  by_cases h : a.toNat / 2 ^ i % 2 = 1
  · simp [h]
  · simp only [h, decide_false, Bool.cond_false, show (0 : UInt64).toNat = 0 from rfl]
    omega

lemma maj_step (x y z : Bool) :
    ((bif x then (1 : UInt64) else 0) &&& (bif y then 1 else 0) |||
        (bif x then 1 else 0) &&& (bif z then 1 else 0) |||
        (bif y then 1 else 0) &&& (bif z then 1 else 0)) =
      bif Arith.Ratatouille.maj x y z then 1 else 0 := by
  cases x <;> cases y <;> cases z <;> rfl

lemma testBit_or_shift (s : UInt64) (c : Bool) {i : ℕ} (hi : i < 64) (j : ℕ) :
    (s ||| (bif c then (1 : UInt64) else 0) <<< i.toUInt64).toNat.testBit j =
      (s.toNat.testBit j || (c && decide (j = i))) := by
  have hi' : i.toUInt64.toNat % 64 = i := by
    rw [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt hi]
  rw [UInt64.toNat_or, Nat.testBit_or, UInt64.toNat_shiftLeft, hi']
  cases c
  · simp
  · rw [show (bif true then (1 : UInt64) else 0).toNat = 1 from rfl, Nat.one_shiftLeft,
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hi), Nat.testBit_two_pow]
    simp [eq_comm]

/-- **The C++ `carries(a, b)`**: bit `j` is the carry `c_{j+1}` of `a + b`. -/
theorem carries_testBit (a b : UInt64) {j : ℕ} (hj : j < 64) :
    (carries a b).toNat.testBit j = cc a b (j + 1) := by
  let step : (UInt64 × UInt64) → ℕ → (UInt64 × UInt64) := fun s i =>
    (a >>> i.toUInt64 &&& 1 &&& (b >>> i.toUInt64 &&& 1) ||| a >>> i.toUInt64 &&& 1 &&& s.1 |||
        b >>> i.toUInt64 &&& 1 &&& s.1,
      s.2 ||| (a >>> i.toUInt64 &&& 1 &&& (b >>> i.toUInt64 &&& 1) |||
        a >>> i.toUInt64 &&& 1 &&& s.1 ||| b >>> i.toUInt64 &&& 1 &&& s.1) <<< i.toUInt64)
  have hc : carries a b = ((List.range 64).foldl step (0, 0)).2 := by
    unfold carries
    simp only [Id.run, ZK.Interp.forIn_range'_foldl, pure_bind, Nat.sub_zero,
      ← List.range_eq_range']
    rfl
  have key : ∀ n ≤ 64, ((List.range n).foldl step (0, 0)).1 = (bif cc a b n then 1 else 0) ∧
      ∀ j, ((List.range n).foldl step (0, 0)).2.toNat.testBit j =
        (decide (j < n) && cc a b (j + 1)) := by
    intro n
    induction n with
    | zero => intro _; exact ⟨rfl, fun j => by simp⟩
    | succ n ih =>
      intro hn
      obtain ⟨h1, h2⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set s := (List.range n).foldl step (0, 0)
      have hk : (step s n).1 = bif cc a b (n + 1) then 1 else 0 := by
        simp only [step, bit_and_one a (show n < 64 by omega), bit_and_one b (show n < 64 by omega),
          h1, maj_step, cc]
      refine ⟨hk, fun j => ?_⟩
      have : (step s n).2 = s.2 ||| (step s n).1 <<< n.toUInt64 := rfl
      rw [this, hk, testBit_or_shift _ _ (show n < 64 by omega), h2]
      by_cases hjn : j = n
      · subst hjn; simp
      · by_cases hjl : j < n
        · simp [hjl, hjn, show j < n + 1 by omega]
        · simp [hjl, hjn, show ¬ j < n + 1 by omega]
  rw [hc, (key 64 le_rfl).2 j]
  simp [hj]

/-! ## Bytes -/

/-- The bytes of a fixed-length string. -/
def bOf {n : ℕ} (v : Spec.Ratatouille.Bytes n) : ByteArray := toBA v.toList

lemma getD_toList_fn {n : ℕ} (v : Spec.Ratatouille.Bytes n) (i : ℕ) :
    v.toList.getD i 0 = v.fn i := by
  rw [List.getD_eq_getElem?_getD, Bytes.fn]
  split_ifs with h
  · simp [h]
  · rw [List.getElem?_eq_none (by simp; omega)]; rfl

lemma fnOf_bOf {n : ℕ} (v : Spec.Ratatouille.Bytes n) : fnOf (bOf v) = v.fn := by
  funext i; rw [bOf, fnOf_toBA, getD_toList_fn]

lemma getD_app_lt {a b : List UInt8} {i : ℕ} (h : i < a.length) : (a ++ b).getD i 0 = a.getD i 0 :=
  List.getD_append _ _ _ _ h

lemma getD_app_ge {a b : List UInt8} {i : ℕ} (h : a.length ≤ i) :
    (a ++ b).getD i 0 = b.getD (i - a.length) 0 :=
  List.getD_append_right _ _ _ _ h

lemma length_committedStates (S : Keccak.State) : (committedStates S).length = 200 := by
  simp [committedStates]

lemma committedStates_getD (S : Keccak.State) {m : ℕ} (hm : m < 100) :
    (committedStates S).getD m 0 = (Keccak.keccakP800Rounds 0 5 S)[m] ∧
      (committedStates S).getD (100 + m) 0 =
        (Keccak.keccakP800Rounds 5 4 (Keccak.keccakP800Rounds 0 5 S))[m] := by
  simp only [committedStates, getD_app, Vector.length_toList, hm, ↓reduceIte, getD_toList _ hm,
    show ¬ 100 + m < 100 by omega, Nat.add_sub_cancel_left, true_and]

/-- The committed states at witness byte `o` are honest (`StatesOK`), if the witness bytes there
are `encode_committed_states S`. -/
lemma statesOK_of (w : Spec.Bytes) (o : ℕ) (S : Keccak.State)
    (h : ∀ m < 200, w.getD (o + m) 0 = (committedStates S).getD m 0) :
    Arith.Ratatouille.StatesOK (Prover.bitOf (toBA w)) o S := by
  refine ⟨Vector.ext fun i hi => ?_, Vector.ext fun i hi => ?_⟩
  · simp only [Keccak.witVec, Keccak.witState, Keccak.stateBits, Vector.getElem_ofFn]
    rw [bitOf_toBA, stateBit_testBit _ hi, show (8 * o + i) / 8 = o + i / 8 by omega,
      show (8 * o + i) % 8 = i % 8 by omega, h _ (by omega),
      (committedStates_getD S (show i / 8 < 100 by omega)).1]
  · simp only [Keccak.witVec, Keccak.witState, Keccak.stateBits, Vector.getElem_ofFn]
    rw [bitOf_toBA, stateBit_rounds9, stateBit_testBit _ hi,
      show (8 * (o + 100) + i) / 8 = o + (100 + i / 8) by omega,
      show (8 * (o + 100) + i) % 8 = i % 8 by omega, h _ (by omega),
      (committedStates_getD S (show i / 8 < 100 by omega)).2]

/-- The commitment state reads `nf`, `ctx`, `r` on their 24, 16, 16 bytes only. -/
lemma comState_congr {nf nf' ctx ctx' r r' : ℕ → UInt8} (t : ℕ) (hnf : ∀ i < 24, nf i = nf' i)
    (hctx : ∀ i < 16, ctx i = ctx' i) (hr : ∀ i < 16, r i = r' i) :
    Arith.Ratatouille.comState nf ctx t r = Arith.Ratatouille.comState nf' ctx' t r' := by
  apply Vector.ext
  intro k hk
  simp only [Arith.Ratatouille.comState, Vector.getElem_ofFn]
  split_ifs <;> first | rfl | exact hr _ (by omega) | exact hctx _ (by omega) |
    exact hnf _ (by omega)

/-- The bits of a credit value in the witness. -/
lemma bit_of_credits (w : Spec.Bytes) (o : ℕ) (v : Credits)
    (h : ∀ i (hi : i < 8), w.getD (o + i) 0 = (encodeCredits v)[i]'hi) {j : ℕ} (hj : j < 64) :
    Prover.bitOf (toBA w) (8 * o + j) = v.toNat.testBit j := by
  rw [bitOf_toBA, show (8 * o + j) / 8 = o + j / 8 by omega,
    show (8 * o + j) % 8 = j % 8 by omega, h _ (by omega)]
  have e := Arith.Ratatouille.encodeCredits_bit v.toNat (j / 8) (j % 8) (Nat.mod_lt _ (by norm_num))
  rw [Nat.div_add_mod] at e
  simp only [encodeCredits, Vector.getElem_ofFn]
  exact e

/-- A credit value read off the witness bits (`creditAt`). -/
lemma creditAt_of (w : Spec.Bytes) (o : ℕ) (v : Credits)
    (h : ∀ i (hi : i < 8), w.getD (o + i) 0 = (encodeCredits v)[i]'hi) :
    Arith.Ratatouille.creditAt (Prover.bitOf (toBA w)) o = v.toNat :=
  Arith.Ratatouille.val_eq_of_bits _ v.toNat_lt fun _ hi => bit_of_credits w o v h hi

/-- The witness bytes read by `bytesAt`. -/
lemma bytesAt_eq (w : Spec.Bytes) (o i : ℕ) :
    Arith.Ratatouille.bytesAt (Prover.bitOf (toBA w)) o i = w.getD (o + i) 0 := by
  rw [Arith.Ratatouille.bytesAt, witByte_bitOf, toBA_get!]

/-! ## Issuance -/

abbrev pI : Params := { witnessBytes := 240, qsDegree := 9, labelRows := true }

/-- The issuance statement with dedicated label rows. -/
def stI (x : IssueInstance) : Statement := ratatouilleIssue (bOf x.c) x.tInit.toNat (bOf x.ctx) true

/-- The issuance witness encoding (`encode_issue_witness`). -/
def encI (x : IssueInstance) (w : IssueWitness) : ByteArray :=
  toBA (encodeIssueWitness w.nf x.ctx x.tInit w.r)

lemma length_encodeIssueWitness (nf : Nullifier) (ctx : Context) (t : Credits) (r : Opening) :
    (encodeIssueWitness nf ctx t r).length = 240 := by
  simp [encodeIssueWitness, length_committedStates]

/-- **The issuance witness satisfies the issuance system** (`Arith.Ratatouille.issue_complete`). -/
theorem issue_holds (x : IssueInstance) (w : IssueWitness) (h : IssueRel x w) :
    (ratatouilleIssueSys (bOf x.c) x.tInit.toNat (bOf x.ctx)).Holds (wSlope pI (encI x w)) := by
  have hw : (encI x w).size = pI.witnessBytes := by
    rw [encI, size_toBA, length_encodeIssueWitness]
  rw [wSlope_eq _ _ hw]
  set S := Arith.Ratatouille.comState w.nf.fn x.ctx.fn x.tInit.toNat w.r.fn with hS
  set L := encodeIssueWitness w.nf x.ctx x.tInit w.r with hL
  have hlen : (w.r.toList ++ w.nf.toList).length = 40 := by simp
  have hr : ∀ i < 16, L.getD i 0 = w.r.fn i := fun i hi => by
    rw [hL, encodeIssueWitness, getD_app_lt (by simp; omega), getD_app_lt (by simp; omega),
      getD_toList_fn]
  have hnf : ∀ i < 24, L.getD (16 + i) 0 = w.nf.fn i := fun i hi => by
    rw [hL, encodeIssueWitness, getD_app_lt (by simp; omega), getD_app_ge (by simp),
      show 16 + i - w.r.toList.length = i by simp, getD_toList_fn]
  have hst : ∀ m < 200, L.getD (40 + m) 0 = (committedStates S).getD m 0 := fun m _ => by
    rw [hL, encodeIssueWitness, getD_app_ge (by rw [hlen]; omega), hlen, Nat.add_sub_cancel_left]
  set wb := Prover.bitOf (toBA L)
  have hE : Arith.Ratatouille.comState (Arith.Ratatouille.bytesAt wb 16) (fnOf (bOf x.ctx))
      x.tInit.toNat (Arith.Ratatouille.bytesAt wb 0) = S :=
    comState_congr _ (fun i hi => by rw [bytesAt_eq, hnf i hi])
      (fun i _ => by rw [fnOf_bOf]) (fun i hi => by rw [bytesAt_eq, Nat.zero_add, hr i hi])
  unfold ratatouilleIssueSys
  obtain ⟨h5, h9⟩ := statesOK_of L 40 S hst
  refine Arith.Ratatouille.issue_complete _ _ _ wb (fun k hk => ?_) ?_ ?_
  · rw [Arith.Ratatouille.commit, hE, fnOf_bOf, Bytes.fn, dite_eq_left (by omega), h, com]
    simp only [Vector.getElem_ofFn, Arith.Ratatouille.commit]
    rfl
  · rw [hE]; exact h5
  · rw [hE]; exact h9

/-! ## Spend -/


abbrev pS : Params := { witnessBytes := 847, qsDegree := 9, labelRows := true }

/-- The spend statement with dedicated label rows (`Verifier.ratatouilleSpend` for the spec's key:
its public map; the spec's key has no digest, so the instance encoding has the other fields). -/
def stS (x : SpendInstance) : Statement where
  params := pS
  dst := toBA (Spec.makeDst "rata" 0 'p' '0')
  instEnc := fun _ => bOf x.nf ++ le64 x.d.toNat ++ bOf x.cNext ++ bOf x.ctx
  comb := some (Arith.Ratatouille.uovM, toBA (Spec.makeDst "rata" 0 'l' '0'))
  values := fun _ lb w =>
    UovEval.ratatouilleSpendValues x.pk (fnOf (bOf x.nf)) x.d.toNat (fnOf (bOf x.cNext))
      (fnOf (bOf x.ctx)) (combinationOf Arith.Ratatouille.uovM lb) w

/-- The spend witness encoding (`encode_spend_witness`). -/
def encS (x : SpendInstance) (w : SpendWitness) : ByteArray :=
  toBA (encodeSpendWitness x.nf w x.d x.ctx)

/-- The spend system, at the combination decoded from the bytes `lb`. -/
def csS (x : SpendInstance) : ByteArray → ByteArray → System GF128 := fun _ lb =>
  Arith.Ratatouille.spendSystem beta GF256.toBits x.pk (fnOf (bOf x.nf)) x.d.toNat
    (fnOf (bOf x.cNext)) (fnOf (bOf x.ctx)) (ofArr (combinationOf Arith.Ratatouille.uovM lb))

lemma stS_values (x : SpendInstance) (c1 lb : ByteArray) (y : ℕ → GF128) :
    (stS x).values c1 lb y = (csS x c1 lb).values y := by
  show UovEval.ratatouilleSpendValues _ _ _ _ _ _ y = _
  rw [UovEval.ratatouilleSpendValues_eq, ← Arith.Ratatouille.spendSystem_values, betaFast_eq]
  rfl

lemma length_encodeSpendWitness (nf : Nullifier) (w : SpendWitness) (d : Credits)
    (ctx : Context) : (encodeSpendWitness nf w d ctx).length = 847 := by
  simp [encodeSpendWitness, length_committedStates]

lemma getD_toList_get {n : ℕ} (v : Spec.Ratatouille.Bytes n) {i : ℕ} (hi : i < n) :
    v.toList.getD i 0 = v[i] := by
  rw [getD_toList_fn, Bytes.fn, dite_eq_left hi]

lemma getD_fn_of {n : ℕ} (v : Spec.Ratatouille.Bytes n) {e i : ℕ} (h : e = i) :
    v.toList.getD e 0 = v.fn i := by
  rw [h, getD_toList_fn]

lemma getD_get_of {n : ℕ} (v : Spec.Ratatouille.Bytes n) {e i : ℕ} (h : e = i) (hi : i < n) :
    v.toList.getD e 0 = v[i] := by
  rw [h, getD_toList_get _ hi]

lemma getD_congr_idx (l : List UInt8) {e m : ℕ} (h : e = m) : l.getD e 0 = l.getD m 0 := by
  rw [h]

/-- **The spend witness layout** (`spend.hpp:92-109`): the fields at their offsets. -/
lemma encodeSpendWitness_getD (nf : Nullifier) (w : SpendWitness) (d : Credits) (ctx : Context) :
    (∀ i < 16, (encodeSpendWitness nf w d ctx).getD i 0 = w.r.fn i) ∧
    (∀ i (hi : i < 8), (encodeSpendWitness nf w d ctx).getD (16 + i) 0 =
      (encodeCredits w.t)[i]'hi) ∧
    (∀ i (hi : i < 8), (encodeSpendWitness nf w d ctx).getD (24 + i) 0 =
      (encodeCredits w.x)[i]'hi) ∧
    (∀ i < 32, (encodeSpendWitness nf w d ctx).getD (32 + i) 0 = (com nf ctx w.t w.r).fn i) ∧
    (∀ i < 24, (encodeSpendWitness nf w d ctx).getD (64 + i) 0 = w.nf'.fn i) ∧
    (∀ i (hi : i < 8), (encodeSpendWitness nf w d ctx).getD (88 + i) 0 =
      (encodeCredits w.t')[i]'hi) ∧
    (∀ i < 16, (encodeSpendWitness nf w d ctx).getD (96 + i) 0 = w.r'.fn i) ∧
    (∀ i < 119, (encodeSpendWitness nf w d ctx).getD (112 + i) 0 = w.s.fn i) ∧
    (∀ i (hi : i < 8), (encodeSpendWitness nf w d ctx).getD (231 + i) 0 =
      (encodeCredits (carries w.t w.x))[i]'hi) ∧
    (∀ i (hi : i < 8), (encodeSpendWitness nf w d ctx).getD (239 + i) 0 =
      (encodeCredits (carries w.t' d))[i]'hi) ∧
    (∀ m < 200, (encodeSpendWitness nf w d ctx).getD (247 + m) 0 = (committedStates
      (Arith.Ratatouille.comState nf.fn ctx.fn w.t.toNat w.r.fn)).getD m 0) ∧
    (∀ m < 200, (encodeSpendWitness nf w d ctx).getD (447 + m) 0 = (committedStates
      (Arith.Ratatouille.tagState (com nf ctx w.t w.r).fn w.x.toNat)).getD m 0) ∧
    (∀ m < 200, (encodeSpendWitness nf w d ctx).getD (647 + m) 0 = (committedStates
      (Arith.Ratatouille.comState w.nf'.fn ctx.fn w.t'.toNat w.r'.fn)).getD m 0) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_,
    fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_,
    fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  all_goals simp only [encodeSpendWitness, getD_app, List.length_append, Vector.length_toList,
    length_committedStates, Nat.reduceAdd]
  · rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
      ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
      ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
      ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega)]
    exact getD_fn_of _ (by omega)
  · rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
      ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
      ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
      ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_right (by omega)]
    exact getD_get_of _ (by omega) hi
  · rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
      ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
      ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
      ite_eq_left (by omega), ite_eq_right (by omega)]
    exact getD_get_of _ (by omega) hi
  · rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
      ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
      ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
      ite_eq_right (by omega)]
    exact getD_fn_of _ (by omega)
  · rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
      ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
      ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_right (by omega)]
    exact getD_fn_of _ (by omega)
  · rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
      ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
      ite_eq_left (by omega), ite_eq_right (by omega)]
    exact getD_get_of _ (by omega) hi
  · rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
      ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
      ite_eq_right (by omega)]
    exact getD_fn_of _ (by omega)
  · rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
      ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_right (by omega)]
    exact getD_fn_of _ (by omega)
  · rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
      ite_eq_left (by omega), ite_eq_right (by omega)]
    exact getD_get_of _ (by omega) hi
  · rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
      ite_eq_right (by omega)]
    exact getD_get_of _ (by omega) hi
  · rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_right (by omega)]
    exact getD_congr_idx _ (by omega)
  · rw [ite_eq_left (by omega), ite_eq_right (by omega)]
    exact getD_congr_idx _ (by omega)
  · rw [ite_eq_right (by omega)]
    exact getD_congr_idx _ (by omega)

/-- **The spend witness satisfies the spend system** for every combination
(`Arith.Ratatouille.spend_complete_gf128`). -/
theorem spend_holds (x : SpendInstance) (w : SpendWitness) (h : SpendRel x w) (c1 lb : ByteArray) :
    (csS x c1 lb).Holds (wSlope pS (encS x w)) := by
  have hw : (encS x w).size = pS.witnessBytes := by
    rw [encS, size_toBA, length_encodeSpendWitness]
  rw [wSlope_eq _ _ hw]
  obtain ⟨hr, ht, hx, hc, hnf', ht', hr', hs, hk1, hk2, hs1, hs2, hs3⟩ :=
    encodeSpendWitness_getD x.nf w x.d x.ctx
  set L := encodeSpendWitness x.nf w x.d x.ctx with hL
  set wb := Prover.bitOf (toBA L)
  have hT : Arith.Ratatouille.creditAt wb 16 = w.t.toNat := creditAt_of L 16 w.t ht
  have hX : Arith.Ratatouille.creditAt wb 24 = w.x.toNat := creditAt_of L 24 w.x hx
  have hT' : Arith.Ratatouille.creditAt wb 88 = w.t'.toNat := creditAt_of L 88 w.t' ht'
  set c := com x.nf x.ctx w.t w.r with hcdef
  have hcfn : ∀ k < 32, c.fn k =
      Arith.Ratatouille.commit x.nf.fn x.ctx.fn w.t.toNat w.r.fn k := fun k hk => by
    rw [hcdef, com, Bytes.fn, dite_eq_left hk]
    simp only [Vector.getElem_ofFn]
  -- The three Keccak inputs.
  have hS1 : Arith.Ratatouille.comState (fnOf (bOf x.nf)) (fnOf (bOf x.ctx))
      (Arith.Ratatouille.creditAt wb 16) (Arith.Ratatouille.bytesAt wb 0) =
      Arith.Ratatouille.comState x.nf.fn x.ctx.fn w.t.toNat w.r.fn := by
    rw [hT, fnOf_bOf, fnOf_bOf]
    exact comState_congr _ (fun _ _ => rfl) (fun _ _ => rfl)
      (fun i hi => by rw [bytesAt_eq, Nat.zero_add, hr i hi])
  have hcom : ∀ k < 32, Arith.Ratatouille.bytesAt wb 32 k =
      Arith.Ratatouille.commit (fnOf (bOf x.nf)) (fnOf (bOf x.ctx))
        (Arith.Ratatouille.creditAt wb 16) (Arith.Ratatouille.bytesAt wb 0) k := fun k hk => by
    rw [bytesAt_eq, hc k hk, hcfn k hk, Arith.Ratatouille.commit, Arith.Ratatouille.commit, hS1]
  have hS2 : Arith.Ratatouille.tagState (Arith.Ratatouille.bytesAt wb 32)
      (Arith.Ratatouille.creditAt wb 24) = Arith.Ratatouille.tagState c.fn w.x.toNat := by
    rw [hX]
    exact Arith.Ratatouille.tagState_congr _ fun k hk => by rw [bytesAt_eq, hc k hk]
  have hS3 : Arith.Ratatouille.comState (Arith.Ratatouille.bytesAt wb 64) (fnOf (bOf x.ctx))
      (Arith.Ratatouille.creditAt wb 88) (Arith.Ratatouille.bytesAt wb 96) =
      Arith.Ratatouille.comState w.nf'.fn x.ctx.fn w.t'.toNat w.r'.fn := by
    rw [hT', fnOf_bOf]
    exact comState_congr _ (fun i hi => by rw [bytesAt_eq, hnf' i hi]) (fun _ _ => rfl)
      (fun i hi => by rw [bytesAt_eq, hr' i hi])
  have hst : Arith.Ratatouille.SpendStates (fnOf (bOf x.nf)) (fnOf (bOf x.ctx)) wb :=
    ⟨by rw [hS1]; exact statesOK_of L 247 _ hs1, by rw [hS2]; exact statesOK_of L 447 _ hs2,
      by rw [hS3]; exact statesOK_of L 647 _ hs3⟩
  -- The carries.
  have hcarry : ∀ (o : ℕ) (a b : Credits),
      (∀ i (hi : i < 8), L.getD (o + i) 0 = (encodeCredits (carries a b))[i]'hi) →
      ∀ i ≤ 64, Arith.Adder.carryB wb o i = cc a b i := by
    intro o a b hk i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rfl
    · rw [Arith.Adder.carryB, ite_eq_right (by omega)]
      refine (bit_of_credits L o _ hk (show i - 1 < 64 by omega)).trans ?_
      rw [carries_testBit _ _ (by omega), Nat.sub_add_cancel hi0]
  have hcar : Arith.Ratatouille.SpendCarries x.d.toNat wb := by
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rw [hcarry 231 w.t w.x hk1 (i + 1) (by omega), hcarry 231 w.t w.x hk1 i (by omega),
        show wb (8 * 16 + i) = w.t.toNat.testBit i from bit_of_credits L 16 w.t ht hi,
        show wb (8 * 24 + i) = w.x.toNat.testBit i from bit_of_credits L 24 w.x hx hi]
      rfl
    · rw [hcarry 239 w.t' x.d hk2 (i + 1) (by omega), hcarry 239 w.t' x.d hk2 i (by omega),
        show wb (8 * 88 + i) = w.t'.toNat.testBit i from bit_of_credits L 88 w.t' ht' hi]
      rfl
  -- The relation.
  obtain ⟨h1, h2, h3⟩ := h
  have hrel : Arith.Ratatouille.SpendRelOf GF256.ofBits x.pk (fnOf (bOf x.nf)) x.d.toNat
      (fnOf (bOf x.cNext)) (fnOf (bOf x.ctx)) wb := by
    rw [Arith.Ratatouille.spendRelOf_gf256_iff]
    refine ⟨fun k => ?_, fun k hk => ?_, ?_, Arith.Ratatouille.creditAt_lt _ _,
      Arith.Ratatouille.creditAt_lt _ _, Arith.Ratatouille.creditAt_lt _ _, x.d.toNat_lt⟩
    · have e := congrArg (fun v => v[k.val]) h1
      simp only [uovEval, tag, Vector.getElem_ofFn] at e
      have hσ := publicMap_congr (N := Arith.Ratatouille.uovN) (M := Arith.Ratatouille.uovM) x.pk
        (σ := fun i => ⟨Keccak.witByte wb (112 + i)⟩) (σ' := fun i => ⟨w.s.fn i⟩) (fun i hi => by
          rw [show Keccak.witByte wb (112 + i) = L.getD (112 + i) 0 from
            (witByte_bitOf _ _).trans (toBA_get! _ _),
            hs i (by simpa [Arith.Ratatouille.uovN] using hi)]) k
      have ht2 : Arith.Ratatouille.tagState (Arith.Ratatouille.commit (fnOf (bOf x.nf))
          (fnOf (bOf x.ctx)) (Arith.Ratatouille.creditAt wb 16) (Arith.Ratatouille.bytesAt wb 0))
          (Arith.Ratatouille.creditAt wb 24) = Arith.Ratatouille.tagState c.fn w.x.toNat := by
        rw [hX]
        exact Arith.Ratatouille.tagState_congr _ fun j hj => by
          rw [← hcom j hj, bytesAt_eq, hc j hj]
      rw [hσ, ht2]
      exact e
    · rw [fnOf_bOf, h2, Bytes.fn, dite_eq_left hk, com, Vector.getElem_ofFn,
        Arith.Ratatouille.commit, Arith.Ratatouille.commit, hS3]
    · rw [hT, hX, hT']; exact h3
  exact Arith.Ratatouille.spend_complete_gf128 x.pk _ x.d.toNat_lt _ _ wb hrel hcom hcar hst _

/-! ## The deterministic hypotheses -/

/-- The issuance system. -/
def csI (x : IssueInstance) : ByteArray → ByteArray → System GF128 :=
  fun _ _ => ratatouilleIssueSys (bOf x.c) x.tInit.toNat (bOf x.ctx)

/-- **`ZKHyp` for issuance**, for every instance and witness of `R_iss`. -/
theorem zkHypI (x : IssueInstance) (w : IssueWitness) (h : IssueRel x w) :
    ZKHyp CrtGen.tables (stI x) (encI x w) (csI x) where
  hvals := ratatouilleIssue_values (bOf x.c) x.tInit.toNat (bOf x.ctx) true
  hdeg := fun _ _ => Degree.ratatouille_issue_deg _ _ _
  hd := show 1 ≤ 9 by decide
  hd' := show 9 + 1 < 2 ^ 64 by decide
  hsat := fun _ _ => issue_holds x w h
  hw := by rw [encI, size_toBA, length_encodeIssueWitness]; rfl
  hnm := show 9 - 1 + 4 ≤ 32 by decide
  hT := maskInvOk_tables
  hI := Interp.interpOk_nine

/-- **`ZKHyp` for spends**, for every instance and witness of `R_spend`. -/
theorem zkHypS (x : SpendInstance) (w : SpendWitness) (h : SpendRel x w) :
    ZKHyp CrtGen.tables (stS x) (encS x w) (csS x) where
  hvals := stS_values x
  hdeg := fun _ _ => Degree.ratatouille_spend_deg _ _ _ _ _ _ _ _
  hd := show 1 ≤ 9 by decide
  hd' := show 9 + 1 < 2 ^ 64 by decide
  hsat := fun c1 lb => spend_holds x w h c1 lb
  hw := by rw [encS, size_toBA, length_encodeSpendWitness]; rfl
  hnm := show 9 - 1 + 4 ≤ 32 by decide
  hT := maskInvOk_tables
  hI := Interp.interpOk_nine

/-! ## The primitives and unlinkability -/

-- The label-row proofs have the sizes of `Sizes.labelRows`.
#guard pI.proofBytes == Sizes.labelRows.issue && pS.proofBytes == Sizes.labelRows.spend
#guard ({ witnessBytes := 240, qsDegree := 9 } : Params).proofBytes == Sizes.main.issue &&
  ({ witnessBytes := 847, qsDegree := 9 } : Params).proofBytes == Sizes.main.spend

/-- A proof as the spec's `n`-byte string (`none` if the prover failed or the length differs). -/
def vecOf (n : ℕ) : Except String ByteArray → Option (Spec.Ratatouille.Bytes n)
  | .ok b => if h : b.size = n then some ⟨b.data, h⟩ else none
  | .error _ => none

/-- **The Lean prover and verifier as Ratatouille's primitives** (label rows, faest-arch-opt's CRT
tables), with any key map and preimage derivation. -/
def leanPrim (Hs : Hashes) {SK : Type} (pk : SK → PublicKey)
    (derive : SK → Target → Option Preimage) : Prim Sizes.labelRows SK where
  pk := pk
  derive := derive
  proveIssue x w ρ := vecOf _ (Prover.prove Hs CrtGen.tables (stI x) (encI x w) (bOf ρ))
  verifyIssue x π := (verify Hs CrtGen.tables (stI x) (bOf π)).accept
  proveSpend x w ρ := vecOf _ (Prover.prove Hs CrtGen.tables (stS x) (encS x w) (bOf ρ))
  verifySpend x π := (verify Hs CrtGen.tables (stS x) (bOf π)).accept

lemma bOf_vec (ρ : Coins 16) : bOf (vec ρ) = ba ρ := by
  rw [bOf, vec, Vector.toList_ofFn, toBA_ofFn]

/-- **Ratatouille unlinkability with the Lean prover** (Theorem 2), on the label-row layout: if the
issuance and spend runs' tapes are `εI`- and `εS`-close to uniform (`TapeHyp`) and the hiding
reductions have advantage `≤ εhide`, any two worlds differ by at most `4εI + 4εS + 2εhide`. Also
assumed: the hash record's output lengths (`unlinkability_label_rows_shake`: none with SHAKE);
BAVC and CRT completeness are theorems (`Bridge.bavcComplete`, `Bridge.crtComplete`). -/
theorem unlinkability_label_rows (A : Adversary Sizes.labelRows) {SK : Type} (pk : SK → PublicKey)
    (derive : SK → Target → Option Preimage) (Hs : Hashes) (hHs : HashesWF Hs)
    {εI εS εhide : ℝ} (hεI : 0 ≤ εI) (hεS : 0 ≤ εS)
    (htI : ∀ x w, IssueRel x w → TapeHyp Hs CrtGen.tables (stI x) (encI x w) εI)
    (htS : ∀ x w, SpendRel x w → TapeHyp Hs CrtGen.tables (stS x) (encS x w) εS)
    (hhide : ∀ b₁ b₂ co, hidingAdv A.ctx (reduction A (fun _ c => vecOf _ (simulate pI c))
      (fun _ c => vecOf _ (simulate pS c)) b₁ b₂ co) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (realGame A (leanPrim Hs pk derive) b₁ b₂) -
        pr _ (realGame A (leanPrim Hs pk derive) b₁' b₂')| ≤ 4 * εI + 4 * εS + 2 * εhide :=
  unlinkability_lean A (leanPrim Hs pk derive) Hs CrtGen.tables stI stS pI pS (fun _ => rfl)
    (fun _ => rfl) rfl rfl encI encS (vecOf _) (vecOf _)
    (fun x w ρ => by simp only [leanPrim, bOf_vec])
    (fun x w ρ => by simp only [leanPrim, bOf_vec])
    csI csS zkHypI zkHypS hHs bavcComplete
    (fun _ _ _ rho => crtComplete Hs _ _ _ rho _ (hlab_of (show 16 ≤ 240 by decide)))
    (fun _ _ _ rho => crtComplete Hs _ _ _ rho _ (hlab_of (show 16 ≤ 847 by decide)))
    hεI hεS htI htS hhide b₁ b₂ b₁' b₂'

/-- **Ratatouille unlinkability with the Lean prover and SHAKE**: only the tape hypotheses and
hiding are assumed. -/
theorem unlinkability_label_rows_shake (A : Adversary Sizes.labelRows) {SK : Type}
    (pk : SK → PublicKey) (derive : SK → Target → Option Preimage)
    {εI εS εhide : ℝ} (hεI : 0 ≤ εI) (hεS : 0 ≤ εS)
    (htI : ∀ x w, IssueRel x w → TapeHyp Hashes.shake CrtGen.tables (stI x) (encI x w) εI)
    (htS : ∀ x w, SpendRel x w → TapeHyp Hashes.shake CrtGen.tables (stS x) (encS x w) εS)
    (hhide : ∀ b₁ b₂ co, hidingAdv A.ctx (reduction A (fun _ c => vecOf _ (simulate pI c))
      (fun _ c => vecOf _ (simulate pS c)) b₁ b₂ co) ≤ εhide)
    (b₁ b₂ b₁' b₂' : Bool) :
    |pr _ (realGame A (leanPrim Hashes.shake pk derive) b₁ b₂) -
        pr _ (realGame A (leanPrim Hashes.shake pk derive) b₁' b₂')| ≤
      4 * εI + 4 * εS + 2 * εhide :=
  unlinkability_label_rows A pk derive Hashes.shake hashesWF_shake hεI hεS htI htS hhide
    b₁ b₂ b₁' b₂'

end VoleMole.Privacy.Ratatouille
