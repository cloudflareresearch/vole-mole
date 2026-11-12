import VoleMole.ZK.HopsJoint
import VoleMole.Privacy.MainChain

/-!
# Zero knowledge on `main`, one proof, in the random-oracle and ideal-cipher model

`ZK/Main.lean` bounds the sibling-label bad event of `main`'s layout (no dedicated label rows; the
CRT gate labels come from the first λ witness rows) by a prediction of `w[0..16)`, for an abstract
model of the view. Here the same argument is made for the **executable prover**, inside the
experiment of `zk_rom_ic` (`ZK/HopsJoint.lean`: `H₃`, `H₂³`, `H₅` and the BAVC's cipher uniform
tables, a distinguisher that reads `H₃`, `H₅` and the cipher at `q₃`, `q₅`, `q_E` keys).

**The hops.** H1, grinding, H4 and the tape steps of `zk_rom_ic` do not use the label rows
(`joint_h1`, `joint_grind`, `joint_h4`, `joint_tape`), nor does the last step (`joint_sim`: the
ideal-tape prover on a uniform tape is the simulator, `proveIdeal_close`). Only H6 does. On `main`:

* `MainP p`: the parameters of `main`'s layout (`labelRows = false`) with at least 16 witness bytes;
  then the label offset `u_pre` is the first 16 bytes of the ideal tape's witness pad `u₀`
  (`uPre_main`), and since the proof's field `d` is `u₀ ⊕ w` (`dB`), `u_pre = d[0..16) ⊕ w[0..16)`
  as a 128-bit block (`uPre_main_dB`, `thetaMain`).
* **`lab_rom_main`** (H5 → H6, the identical-until-bad coupling, from `lab_rom`): the ideal-tape
  prover with the sibling answers recomputed from the `H₅` table and the one with uniform sibling
  answers are at most `Pr[bad]` apart, where `bad` is "the prover or the distinguisher reads `H₅`
  at a sibling input". Each such read names one candidate for `u_pre` (`guessSet`, as in
  `HopsH6.guesses`), so `bad` implies `thetaMain d w[0..16) ∈ guessSet …`; and on a uniform tape the
  proof's fields (`fieldsOf`, which contain `d`) are uniform (`upush_fieldsOf`). So the bound is
  the probability that the **witness prefix `w[0..16)` lies in the candidate set
  `{r | thetaMain d r ∈ guessSet …}` computed from the simulated proof `(s, f)` and the tables
  alone**: the success probability of an explicit, witness-free predictor of `w[0..16)` (`mainPred`).
  The candidate set has at most `q₅ + 1` elements (`card_candidates_le`).
* **`zk_rom_ic_main`**: one proof of `proveE` (the `zk_rom_ic` prover; the executable prover at
  AES, `proveE_recOf_aes`) on `main` is
  `q₃·2⁻¹²⁸ + 221·(4607 + q_E)·2⁻¹²⁸ + Pr[mainPred]`-close to the simulator.

So for one proof ZK on `main` holds exactly to the extent that the distinguisher cannot predict
the first 16 witness bytes: this is condition (PU) of `lean/docs/zk.md` §4.1, here with the oracle
adversary reduced to its query function (the read sets `Q5`) and every hybrid mechanized. A
distinguisher that knows `w[0..16)` reads one sibling input and makes `Pr[mainPred] = 1`
(`lean/docs/zk.md` Prop. 4.1): per-proof zero knowledge against witness-knowing distinguishers is
false on `main`, and the bound is the right one. **`mainPred_le_uniform`**: when the prefix is a
uniform secret independent of the predictor's inputs, the term is at most `(q₅ + 1)·2⁻¹²⁸`, as with
label rows. Several proofs that share the prefix (a token's issuance and redemption) are treated
jointly in `Privacy/MainChain.lean`.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

set_option linter.unusedSectionVars false
-- (The linter's traversal of the large product types below exceeds the recursion limit.)
set_option linter.constructorNameAsVariable false

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy

attribute [local instance] decEqW128

/-! ## The label offset on `main` -/

section Theta

/-- **`main`'s layout**: no dedicated label rows (the gate labels come from the first λ witness
rows), and at least 16 witness bytes (all five relations have far more). -/
structure MainP (p : Params) : Prop where
  hlr : p.labelRows = false
  hw : 16 ≤ p.witnessBytes

variable {p : Params}

lemma MainP.offset (h : MainP p) : p.labelRowOffset = 0 := by
  simp [Params.labelRowOffset, h.hlr]

lemma MainP.corrRows (h : MainP p) : p.correctionRows = 8 * p.witnessBytes := by
  simp [Params.correctionRows, Params.witnessBits, h.hlr]

lemma MainP.corrBytes (h : MainP p) : p.correctionBytes = p.witnessBytes := by
  simp only [Params.correctionBytes, h.corrRows]; omega

lemma MainP.hlab (h : MainP p) : p.labelRowOffset + 128 ≤ p.correctionRows := by
  rw [h.offset, h.corrRows]; have := h.hw; omega

/-- 16 bytes as a 128-bit block (bit `k` is bit `k % 8` of byte `k / 8`, as `wordAt` reads them). -/
def w16 (b : Bytes 16) : W128 := ⟨wordAt (wordsOf (ba b)) 0, wordAt (wordsOf (ba b)) 64⟩

lemma wbit_w16 (b : Bytes 16) {k : ℕ} (hk : k < 128) :
    wbit (wordsOf (ba b)) k = (b ⟨k / 8, by omega⟩).toNat.testBit (k % 8) := by
  rw [wbit_wordsOf _ (by rw [size_ba]; omega), get!_ba _ (by omega)]

/-- **`w16` is injective.** -/
lemma w16_injective : Function.Injective w16 := by
  intro b b' h
  have hlo := congrArg W128.lo h
  have hhi := congrArg W128.hi h
  simp only [w16] at hlo hhi
  funext j
  have hj := j.isLt
  apply UInt8.toNat_inj.1
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 8
  · have key : ∀ c : Bytes 16, (c j).toNat.testBit i = wbit (wordsOf (ba c)) (8 * j + i) := by
      intro c
      rw [wbit_w16 c (by omega)]
      have e1 : (8 * j.val + i) / 8 = j.val := by omega
      have e2 : (8 * j.val + i) % 8 = i := by omega
      simp only [e1, e2, Fin.eta]
    rw [key b, key b']
    by_cases h64 : 8 * j.val + i < 64
    · rw [← Nat.zero_add (8 * j.val + i), ← wordAt_testBit _ _ h64, ← wordAt_testBit _ _ h64, hlo]
    · have e : 8 * j.val + i = 64 + (8 * j.val + i - 64) := by omega
      rw [e, ← wordAt_testBit _ _ (by omega), ← wordAt_testBit _ _ (by omega), hhi]
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (b j).toNat_lt
        (Nat.pow_le_pow_right (by norm_num) (show 8 ≤ i by omega))),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (b' j).toNat_lt
        (Nat.pow_le_pow_right (by norm_num) (show 8 ≤ i by omega)))]

/-- The first 16 bytes of a block of at least 16 bytes. -/
def pre16 {n : ℕ} (h : 16 ≤ n) (b : Bytes n) : Bytes 16 := fun k => b ⟨k, by omega⟩

/-- The first 16 bytes of a byte string (the witness prefix `w[0..16)`). -/
def wPre (w : ByteArray) : Bytes 16 := fun k => w.get! k

/-- Byte-wise exclusive or of two 16-byte blocks. -/
def xor16 (a b : Bytes 16) : Bytes 16 := fun k => a k ^^^ b k

/-- **The label offset on `main`, from `d[0..16)` and `w[0..16)`.** -/
def thetaMain (d r : Bytes 16) : W128 := w16 (xor16 d r)

lemma thetaMain_injective (d : Bytes 16) : Function.Injective (thetaMain d) := by
  intro r r' h
  have h1 := w16_injective h
  funext k
  have := congrFun h1 k
  simp only [xor16] at this
  exact (UInt8.xor_right_inj _).1 this

/-- **On `main`, `u_pre` is the first 16 bytes of the witness pad `u₀`.** -/
lemma uPre_main (h : MainP p) (t : Pads p) : uPreOf p (usOf p t)[0]! = w16 (pre16 h.hw t.1) := by
  have hc := cb_add_nMask_le p
  have key : ∀ k < 128, wbit (usOf p t)[0]! k = wbit (wordsOf (ba (pre16 h.hw t.1))) k := by
    intro k hk
    have hw := h.hw
    have hcb := h.corrBytes
    rw [wbit_usOf t (by decide) (by omega), usBytes_get_corr t (by decide) (by omega),
      wbit_w16 _ hk]
    simp only [↓reduceDIte, U0, get!_append, size_ba, show k / 8 < p.witnessBytes by omega,
      ↓reduceIte, get!_ba _ (show k / 8 < p.witnessBytes by omega)]
    rfl
  simp only [uPreOf, w16, h.offset]
  congr 1
  · exact wordAt_congr fun k hk => by rw [Nat.zero_add]; exact key k (by omega)
  · exact wordAt_congr fun k hk => key (64 + k) (by omega)

/-- **`u_pre = d[0..16) ⊕ w[0..16)`** (with `d = dB w t`, the proof's witness correction). -/
lemma uPre_main_dB (h : MainP p) (w : ByteArray) (t : Pads p) :
    uPreOf p (usOf p t)[0]! = thetaMain (pre16 h.hw (dB w t)) (wPre w) := by
  rw [uPre_main h]
  unfold thetaMain
  congr 1
  funext k
  simp only [pre16, xor16, dB, wPre, UInt8.xor_assoc, UInt8.xor_self, UInt8.xor_zero]

end Theta

/-! ## The bad event as a prediction of `w[0..16)` -/

section Bad

variable (Hs : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)
  (cs : ByteArray → ByteArray → System GF128)

/-- **The candidates for `u_pre`** from a set `S` of `H₅` table keys: zero (the prover's own reads)
and each key's guess (`guessOf`, a function of the shared tape and the proof's fields). -/
noncomputable def guessSet (S : Finset (SKey st.params)) (s : Shared) (f : SimFields st.params) :
    Finset W128 :=
  insert W128.zero (S.biUnion (guessOf Hs T st s f))

lemma card_guessSet_le (S : Finset (SKey st.params)) (s : Shared) (f : SimFields st.params) :
    (guessSet Hs T st S s f).card ≤ S.card + 1 := by
  unfold guessSet
  refine (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ?_)
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ k ∈ S, (guessOf Hs T st s f k).card ≤ ∑ _k ∈ S, 1 :=
        Finset.sum_le_sum fun k _ => card_guessOf_le Hs T st s f k
    _ = S.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]

/-- **A sibling input in `S` or among the prover's reads is a correct guess of `u_pre`**
(`bad_mem_guesses` for any key set). -/
lemma bad_mem_guessSet (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    (Hs' : Hashes) (S : Finset (SKey st.params)) (s : Shared) (t : Pads st.params)
    (hbad : ∃ e, sibKey Hs T st (s, dropSib t) e ∈ proverKeys Hs T st (s, t) ∪ S) :
    uPreOf st.params (usOf st.params t)[0]! ∈ guessSet Hs T st S s
      (fieldsOf Hs' T st w cs s (hitOf s).1 (hitOf s).2 t).1 := by
  obtain ⟨e, he⟩ := hbad
  have hsib : sEnc Hs T st (sibKey Hs T st (s, dropSib t) e) = sibInput Hs T st s t e := by
    rw [sibKey, enc_keyOf (sEnc Hs T st)]; rfl
  rw [Finset.mem_union] at he
  unfold guessSet
  rw [Finset.mem_insert]
  rcases he with he | he
  · left
    rw [mem_proverKeys, hsib] at he
    exact uPre_zero_of_sib_mem Hs T st hlab s t e he
  · right
    rw [Finset.mem_biUnion]
    refine ⟨_, he, mem_guessOf Hs T st (e := e) ?_⟩
    rw [hsib, sibInput_eq Hs T st hlab, qcolsTape_eq_qcolsF]

/-- **The candidate set of the witness prefix**: the 16-byte values `r` with `thetaMain d r` a
candidate for `u_pre`, `d = f`'s `d[0..16)`. A function of the shared tape, the fields and `S`
only. -/
noncomputable def candidates (hm : MainP st.params) (S : Finset (SKey st.params)) (s : Shared)
    (f : SimFields st.params) : Finset (Bytes 16) :=
  univ.filter fun r => thetaMain (pre16 hm.hw f.2.2.2.1) r ∈ guessSet Hs T st S s f

lemma mem_candidates (hm : MainP st.params) {S : Finset (SKey st.params)} {s : Shared}
    {f : SimFields st.params} {r : Bytes 16} :
    r ∈ candidates Hs T st hm S s f ↔ thetaMain (pre16 hm.hw f.2.2.2.1) r ∈ guessSet Hs T st S s f := by
  unfold candidates
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

/-- **At most `|S| + 1` candidates.** -/
lemma card_candidates_le (hm : MainP st.params) (S : Finset (SKey st.params)) (s : Shared)
    (f : SimFields st.params) : (candidates Hs T st hm S s f).card ≤ S.card + 1 := by
  refine le_trans ?_ (card_guessSet_le Hs T st S s f)
  refine Finset.card_le_card_of_injOn (thetaMain (pre16 hm.hw f.2.2.2.1)) (fun r hr => ?_)
    (fun r _ r' _ h => thetaMain_injective _ h)
  rw [mem_coe, mem_candidates] at hr
  exact hr

end Bad

/-! ## H6 on `main` -/

lemma pr_prod_le_prod {α β β' : Type*} [Fintype α] [Fintype β] [Fintype β'] [Nonempty α]
    (P : α × β → Prop) (Q : α × β' → Prop)
    (h : ∀ a, pr β (fun b => P (a, b)) ≤ pr β' (fun b => Q (a, b))) :
    pr (α × β) P ≤ pr (α × β') Q := by
  rw [pr_prod, pr_prod]
  have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  gcongr with a
  exact h a

section H6

variable (Hs : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)
  (cs : ByteArray → ByteArray → System GF128)
  (QD : Except String ByteArray → (SKey st.params → Bytes 4) → Finset (SKey st.params))

/-- **The predictor's success event** for one proof: with the shared tape `s`, the simulated
fields `f` and the `H₅` table `G`, the witness prefix lies in the candidate set of the keys the
distinguisher reads on the simulated proof `outOf st s f`. -/
def predEv (hm : MainP st.params) (r : Bytes 16) (x : (Shared × SimFields st.params) ×
    (SKey st.params → Bytes 4)) : Prop :=
  r ∈ candidates Hs T st hm (QD (outOf st x.1.1 x.1.2) x.2) x.1.1 x.1.2

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024 in
/-- **For a fixed shared tape and table, the bad event is a prediction** of `w[0..16)` from the
uniform fields. -/
theorem pr_bad_main (hm : MainP st.params) (h : ZKHyp T st w cs) (G : SKey st.params → Bytes 4)
    (s : Shared) :
    pr (Pads st.params) (fun t => ∃ e, sibKey Hs T st (s, dropSib t) e ∈
      proverKeys Hs T st (s, t) ∪ QD (proveIdeal (H5 Hs T st G) T st w (s, t)) G) ≤
      pr (SimFields st.params) (fun f => predEv Hs T st QD hm (wPre w) ((s, f), G)) := by
  let F := fieldsOf (H5 Hs T st G) T st w cs s (hitOf s).1 (hitOf s).2
  let Ev : SimFields st.params → Prop := fun f => predEv Hs T st QD hm (wPre w) ((s, f), G)
  have e1 : pr (Pads st.params) (fun t => ∃ e, sibKey Hs T st (s, dropSib t) e ∈
      proverKeys Hs T st (s, t) ∪ QD (proveIdeal (H5 Hs T st G) T st w (s, t)) G) ≤
      pr (Pads st.params) (fun t => Ev (F t).1) := by
    refine pr_mono fun t ht => ?_
    have hm' := bad_mem_guessSet Hs T st w cs hm.hlab (H5 Hs T st G) _ s t ht
    rw [uPre_main_dB hm w t] at hm'
    show wPre w ∈ candidates Hs T st hm _ s (F t).1
    rw [mem_candidates]
    rw [← proveIdeal_eq_outOf T st w cs _ h]
    exact hm'
  have e2 : pr (Pads st.params) (fun t => Ev (F t).1) =
      pr (SimFields st.params × Bytes (labelBytes st.params)) (fun y => Ev y.1) := by
    have := (upush_fieldsOf (H5 Hs T st G) T st w cs s (hitOf s).1 (hitOf s).2 h.hT h.hnm)
      (fun y => Ev y.1)
    rw [abs_nonpos_iff, sub_eq_zero] at this
    exact this
  rw [e2, pr_prod_fst] at e1
  exact e1

set_option synthInstance.maxSize 1024 in
/-- **H6 on `main`** (the identical-until-bad coupling of H5 and H6, `lab_rom`, with the bad event
bounded by the prediction `predEv`): the ideal-tape prover with the sibling answers recomputed
from a uniform `H₅` table and the one with uniform sibling answers, against a distinguisher that
reads the table at the keys `QD`, are at most `Pr[predEv]` apart. -/
theorem lab_rom_main (hm : MainP st.params) (h : ZKHyp T st w cs)
    (D : Except String ByteArray → (SKey st.params → Bytes 4) → Prop)
    (hQD : ∀ o G G', (∀ k ∈ QD o G, G k = G' k) → (D o G ↔ D o G')) :
    |pr (IdealTape st.params × (SKey st.params → Bytes 4)) (fun x =>
        D (proveIdeal (H5 Hs T st x.2) T st w (fillSib (H5 Hs T st x.2) T st x.1)) x.2) -
      pr (IdealTape st.params × (SKey st.params → Bytes 4))
        (fun x => D (proveIdeal (H5 Hs T st x.2) T st w x.1) x.2)| ≤
      pr ((Shared × SimFields st.params) × (SKey st.params → Bytes 4))
        (predEv Hs T st QD hm (wPre w)) := by
  let E2 : ((Shared × PadsU st.params) × (SKey st.params → Bytes 4)) × Sib ≃
      IdealTape st.params × (SKey st.params → Bytes 4) :=
    { toFun := fun y => ((y.1.1.1, withSib y.1.1.2 y.2), y.1.2)
      invFun := fun x => (((x.1.1, dropSib x.1.2), x.2), x.1.2.2.2.2.2.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let E3 : (Shared × PadsU st.params) × ((SKey st.params → Bytes 4) × Sib) ≃
      IdealTape st.params × (SKey st.params → Bytes 4) :=
    { toFun := fun y => ((y.1.1, withSib y.1.2 y.2.2), y.2.1)
      invFun := fun x => ((x.1.1, dropSib x.1.2), (x.2, x.1.2.2.2.2.2.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have e1 : pr (IdealTape st.params × (SKey st.params → Bytes 4)) (fun x =>
      D (proveIdeal (H5 Hs T st x.2) T st w (fillSib (H5 Hs T st x.2) T st x.1)) x.2) =
      pr ((Shared × PadsU st.params) × (SKey st.params → Bytes 4)) (fun x =>
        D (proveIdeal (H5 Hs T st x.2) T st w (fillSib (H5 Hs T st x.2) T st
          (x.1.1, withSib x.1.2 fun _ => fun _ => 0))) x.2) := by
    rw [← pr_equiv E2, ← pr_prod_fst (β := Sib) (fun x : (Shared × PadsU st.params) ×
      (SKey st.params → Bytes 4) => D (proveIdeal (H5 Hs T st x.2) T st w (fillSib (H5 Hs T st x.2)
        T st (x.1.1, withSib x.1.2 fun _ => fun _ => 0))) x.2)]
    refine pr_congr fun y => ?_
    show D (proveIdeal (H5 Hs T st y.1.2) T st w (fillSib (H5 Hs T st y.1.2) T st
        (y.1.1.1, withSib y.1.1.2 y.2))) y.1.2 ↔ _
    rw [fillSib_withSib T st _ y.1.1.1 y.1.1.2 y.2 fun _ => fun _ => 0]
  have e2 : pr (IdealTape st.params × (SKey st.params → Bytes 4))
      (fun x => D (proveIdeal (H5 Hs T st x.2) T st w x.1) x.2) =
      pr ((Shared × PadsU st.params) × ((SKey st.params → Bytes 4) × Sib))
        (fun x => D (proveIdeal (H5 Hs T st x.2.1) T st w (x.1.1, withSib x.1.2 x.2.2)) x.2.1) :=
    (pr_equiv E3 _).symm
  rw [e1, e2]
  refine (lab_rom Hs T st (fun t G => D (proveIdeal (H5 Hs T st G) T st w t) G)
    (fun t G => proverKeys Hs T st t ∪ QD (proveIdeal (H5 Hs T st G) T st w t) G)
    fun t G G' hG => ?_).trans ?_
  · have hp := proveIdeal_table_congr Hs T st w hm.hlab t G G' fun k hk =>
      hG k (Finset.mem_union_left _ hk)
    show D (proveIdeal (H5 Hs T st G) T st w t) G ↔ D (proveIdeal (H5 Hs T st G') T st w t) G'
    rw [hp]
    refine hQD _ G G' fun k hk => hG k (Finset.mem_union_right _ ?_)
    rw [hp]; exact hk
  · let E : (SKey st.params → Bytes 4) × IdealTape st.params ≃
        (Shared × PadsU st.params) × ((SKey st.params → Bytes 4) × Sib) :=
      { toFun := fun y => ((y.2.1, dropSib y.2.2), (y.1, y.2.2.2.2.2.2.2.2))
        invFun := fun x => (x.2.1, (x.1.1, withSib x.1.2 x.2.2))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let E' : (SKey st.params → Bytes 4) × (Shared × SimFields st.params) ≃
        (Shared × SimFields st.params) × (SKey st.params → Bytes 4) := Equiv.prodComm _ _
    rw [← pr_equiv E, ← pr_equiv E']
    refine pr_prod_le_prod _ _ fun G => pr_prod_le_prod _ _ fun s => ?_
    exact pr_bad_main Hs T st w cs QD hm h G s

end H6

/-! ## Records that agree off the unread domains -/

section Congr

variable {k : Kind} {Hs Hs' : Hashes} (hu : Unread k) (h : Hs.AgreeOff k Hs') (T : CrtTables)
  (st : Statement)
include hu h

lemma guessOf_agreeOff : guessOf Hs T st = guessOf Hs' T st := by
  have hP := h.pubOf' hu st
  have hE := sEnc_agreeOff hu h T st
  funext s f k
  unfold guessOf qcolsF
  rw [hP, hE]

lemma guessSet_agreeOff : guessSet Hs T st = guessSet Hs' T st := by
  funext S s f
  simp only [guessSet, guessOf_agreeOff hu h]

lemma candidates_agreeOff : candidates Hs T st = candidates Hs' T st := by
  funext hm S s f
  simp only [candidates, guessSet_agreeOff hu h]

end Congr

/-! ## The chain on `main` -/

section Chain

variable (Hb : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)

/-- **The predictor of `zk_rom_ic_main`**: on the simulator's coins `(s, f)` and independent
tables `(G3, E, G5)`, the witness prefix `r` lies in the candidate set of the `H₅` keys `Q5` that
the distinguisher reads on the simulated proof. Nothing here depends on the witness but `r`. -/
def mainPred (hm : MainP st.params)
    (Q5 : Except String ByteArray → Tab3 → Tab5 st.params → Cipher → Finset (SKey st.params))
    (r : Bytes 16) (x : (Tab3 × Cipher) × ((Shared × SimFields st.params) × Tab5 st.params)) :
    Prop :=
  r ∈ candidates Hb T st hm (Q5 (outOf st x.2.1.1 x.2.1.2) x.1.1 x.2.2 x.1.2) x.2.1.1 x.2.1.2

set_option synthInstance.maxSize 1024 in
/-- **H6 on `main` with the tables**: `joint_h6` with the bad event the prediction `mainPred`. -/
theorem joint_h6_main {cs : ByteArray → ByteArray → System GF128} (hm : MainP st.params)
    (hzk : ZKHyp T st w cs) (D : Except String ByteArray → Vis st.params → Prop)
    (Q5 : Except String ByteArray → Tab3 → Tab5 st.params → Cipher → Finset (SKey st.params))
    (hQ5 : ∀ o G3 G5 G5' E, (∀ k ∈ Q5 o G3 G5 E, G5 k = G5' k) →
      (D o (G3, G5, E) ↔ D o (G3, G5', E))) :
    |pr (IdealTape st.params × Vis st.params) (fun c =>
        D (proveIdeal (recP Hb T st w c.2.1 c.2.2.1) T st w
          (fillSib (recP Hb T st w c.2.1 c.2.2.1) T st c.1)) c.2) -
      pr (IdealTape st.params × Vis st.params) (fun c =>
        D (proveIdeal (recP Hb T st w c.2.1 c.2.2.1) T st w c.1) c.2)| ≤
      pr ((Tab3 × Cipher) × ((Shared × SimFields st.params) × Tab5 st.params))
        (mainPred Hb T st hm Q5 (wPre w)) := by
  let E6 : (Tab3 × Cipher) × (IdealTape st.params × Tab5 st.params) ≃
      IdealTape st.params × Vis st.params :=
    { toFun := fun c => (c.2.1, (c.1.1, (c.2.2, c.1.2)))
      invFun := fun c => ((c.2.1, c.2.2.2), (c.1, c.2.2.1))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv E6, ← pr_equiv E6]
  refine abs_pr_prod_sub_le_pr _ _ _ fun a => ?_
  obtain ⟨G3, E⟩ := a
  have h := lab_rom_main ((Hb.withTable .h3 (seedInput (st.mu1 Hb)
      (w.extract 0 st.params.witnessBytes)) G3).withTable .h23 (gEnc fun _ => ByteArray.empty)
      fun _ => 0) T st w cs (fun o G5 => Q5 o G3 G5 E) hm hzk (fun o G5 => D o (G3, G5, E))
    (fun o G5 G5' hk => hQ5 o G3 G5 G5' E hk)
  simp only [← recP_eq_H5] at h
  refine h.trans (le_of_eq (pr_congr fun x => ?_))
  have a1 : ((Hb.withTable .h3 (seedInput (st.mu1 Hb)
      (w.extract 0 st.params.witnessBytes)) G3).withTable .h23 (gEnc fun _ => ByteArray.empty)
      fun _ => 0).AgreeOff .h23 (Hb.withTable .h3 (seedInput (st.mu1 Hb)
      (w.extract 0 st.params.witnessBytes)) G3) :=
    ((Hb.withTable .h3 _ G3).agreeOff_withTable .h23 _ _).symm
  have a2 : (Hb.withTable .h3 (seedInput (st.mu1 Hb)
      (w.extract 0 st.params.witnessBytes)) G3).AgreeOff .h3 Hb :=
    (Hb.agreeOff_withTable .h3 _ G3).symm
  unfold predEv mainPred
  rw [candidates_agreeOff unread_h23 a1, candidates_agreeOff unread_h3 a2]

/-- **Zero knowledge on `main`, one proof, in the combined random-oracle and ideal-cipher model.**
The experiment of `zk_rom_ic` (the same prover `proveE`, tables, distinguisher and read sets), for
a statement of `main`'s layout (`MainP`): the advantage is at most

    q₃·2⁻¹²⁸ + 221·(4607 + q_E)·2⁻¹²⁸ + Pr[mainPred]

where `Pr[mainPred]` is the probability that the explicit witness-free predictor (the
distinguisher's `H₅` read set on a simulated proof and independent tables, turned into at most
`q₅ + 1` candidates for `w[0..16)`, `card_candidates_le`) contains the witness prefix. -/
theorem zk_rom_ic_main {cs : ByteArray → ByteArray → System GF128} (hm : MainP st.params)
    (hzk : ZKHyp T st w cs) (hp : SmallParams st.params)
    (pre : Tab5 st.params → Cipher → Bytes 16 × Bytes 16 → ByteArray)
    (D : Except String ByteArray → Vis st.params → Prop)
    (Q3 : Except String ByteArray → Tab3 → Tab5 st.params → Cipher → Finset (Bytes 16))
    (hQ3 : ∀ o G3 G3' G5 E, (∀ k ∈ Q3 o G3 G5 E, G3 k = G3' k) →
      (D o (G3, G5, E) ↔ D o (G3', G5, E)))
    {q3 : ℕ} (hq3 : ∀ o G3 G5 E, (Q3 o G3 G5 E).card ≤ q3)
    (Q5 : Except String ByteArray → Tab3 → Tab5 st.params → Cipher → Finset (SKey st.params))
    (hQ5 : ∀ o G3 G5 G5' E, (∀ k ∈ Q5 o G3 G5 E, G5 k = G5' k) →
      (D o (G3, G5, E) ↔ D o (G3, G5', E)))
    (QE : Except String ByteArray → Tab3 → Tab5 st.params → Cipher → Finset Blk)
    (hQE : ∀ o G3 G5 E E', (∀ k ∈ QE o G3 G5 E, E k = E' k) →
      (D o (G3, G5, E) ↔ D o (G3, G5, E')))
    {qE : ℕ} (hqE : ∀ o G3 G5 E, (QE o G3 G5 E).card ≤ qE) :
    |pr ((Bytes 16 × Tab2) × Vis st.params) (fun c =>
        D (proveE (recOf Hb T st w (pre c.2.2.1 c.2.2.2) c.2.1 c.1.2 c.2.2.1) T st w c.2.2.2
          (pre c.2.2.1 c.2.2.2) c.1.1) c.2) -
      pr (SimCoins st.params × Vis st.params) (fun c => D (simulate st.params c.1) c.2)| ≤
      q3 / 2 ^ 128 + 221 * (4607 + qE) / 2 ^ 128 +
        pr ((Tab3 × Cipher) × ((Shared × SimFields st.params) × Tab5 st.params))
          (mainPred Hb T st hm Q5 (wPre w)) := by
  have h1 := joint_h1 Hb T st w pre D Q3 hQ3 hq3
  have h2 := joint_grind Hb T st w pre D
  have h3 := joint_h4 Hb T st w hp D QE hQE hqE
  have h4 := joint_tape Hb T st w D
  have h5 := joint_h6_main Hb T st w hm hzk D Q5 hQ5
  have h6 := joint_sim Hb T st w hzk D
  exact (abs_chain6 h1 h2 h3 h4 h5 h6).trans (le_of_eq (by ring))

end Chain

/-! ## A uniform prefix: the label-row bound -/

/-- **(PU) holds statistically for a uniform prefix**: if the witness prefix `r` is uniform and
independent of the predictor's inputs `x`, a candidate set of at most `q + 1` elements contains it
with probability at most `(q + 1)·2⁻¹²⁸`. -/
theorem pr_mem_uniform_le {X : Type*} [Fintype X] [Nonempty X] (C : X → Finset (Bytes 16)) {q : ℕ}
    (hC : ∀ x, (C x).card ≤ q + 1) :
    pr (Bytes 16 × X) (fun z => z.1 ∈ C z.2) ≤ (q + 1) / 2 ^ 128 := by
  have := pr_mem_indep_le (α := Bytes 16) (β := X) id (fun _ _ h => h) C hC
  rw [Prob.card_bytes] at this
  refine this.trans (le_of_eq ?_)
  push_cast
  norm_num

end VoleMole.ZK.Sim
