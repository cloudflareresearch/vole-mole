import VoleMole.ZK.HopsRead

/-!
# H6 in the ROM against a distinguisher that reads `H₅` (`lean/docs/zk.md` H6)

`lab_rom` (`ZK/HopsROM.lean`) bounds the H6 hop (sibling answers recomputed from a uniform `H₅`
table against uniform ones) by the probability that the run reads a sibling input. Here that
probability is bounded for the ideal-tape prover followed by a distinguisher `D` that reads the
`H₅` table at `q₅` keys of its choice (adaptively: its query set may depend on the table), with
dedicated label rows:

* the prover reads `H₅` only at the active inputs `iv ‖ e ‖ L_e(q) ‖ 5` (`proveIdeal_h5_congr`),
  and the sibling input of gate `e` is `iv ‖ e ‖ (L_e(q) ⊕ u_pre) ‖ 5` (`sibInput_eq`), so the
  prover reads one only if `u_pre = 0`;
* a query of `D` is a sibling input only if `u_pre` is the one offset (`guess`) that turns the
  active label of the query's gate into the query's label, which is a function of the proof's
  fields and of the shared tape (`L_e(q)` is computed from the opening, `Δ` and the corrections);
* `u_pre` is the label-row pad `Θ` (`uPre_eq_thetaW`, injectively), and `Θ` is uniform and
  independent of the proof's fields (`upush_fieldsOf`, as for `prove_guess_theta`).

**`lab_rom_query`**, **`lab_rom_hyp`** (the ROM analogue of `LabHyp`): `ε_lab ≤ (q₅ + 1)·2⁻¹²⁸`,
zk.md §3's `(Q₅ + n_mult·Q_V + Q_P)·2⁻¹²⁸` for one proof (`Q_P = 1`: the prover's own reads, a
sibling input only if `Θ = 0`; `q₅` counts all of `D`'s `H₅` queries, including those of the
verifications it runs).
-/

open Finset

namespace VoleMole.ZK.Sim

-- The statements hold for any CTR PRG (`HasPrg`, `Verifier/Prg.lean`), AES included.
variable [VoleMole.Verifier.HasPrg]
set_option linter.unusedSectionVars false

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy

/-! ## `u_pre` is the label-row pad -/

section Theta

variable {p : Params}

lemma labelRows_sizes (hlr : p.labelRows = true) :
    p.labelRowOffset = 8 * p.witnessBytes ∧ p.correctionBytes = p.witnessBytes + 16 ∧
      labelBytes p = 16 ∧ p.correctionRows = 8 * p.witnessBytes + 128 := by
  have h1 : p.labelRowOffset = 8 * p.witnessBytes := by
    simp only [Params.labelRowOffset, Params.witnessBits, hlr, ↓reduceIte]
  have h2 : p.correctionRows = 8 * p.witnessBytes + 128 := by
    simp only [Params.correctionRows, Params.witnessBits, hlr, ↓reduceIte]
  have h3 : p.correctionBytes = p.witnessBytes + 16 := by
    simp only [Params.correctionBytes, h2]; omega
  exact ⟨h1, h3, by simp only [labelBytes, h3]; omega, h2⟩

/-- Bit `k` of `u`'s label rows is bit `k` of the label-row pad `Θ`. -/
lemma wbit_u0_label (hlr : p.labelRows = true) (t : Pads p) {k : ℕ} (hk : k < 128) :
    wbit (usOf p t)[0]! (p.labelRowOffset + k) = ((ba t.2.1).get! (k / 8)).toNat.testBit (k % 8) := by
  obtain ⟨ho, hcb, -, hcr⟩ := labelRows_sizes hlr
  have hrl := correctionRows_lt p
  rw [wbit_usOf t (by decide) (by omega), usBytes_get_corr t (by decide) (by omega)]
  simp only [↓reduceDIte, U0, get!_append, size_ba, ho,
    show ¬ (8 * p.witnessBytes + k) / 8 < p.witnessBytes by omega, ↓reduceIte,
    show (8 * p.witnessBytes + k) / 8 - p.witnessBytes = k / 8 by omega,
    show (8 * p.witnessBytes + k) % 8 = k % 8 by omega]

/-- The pads with label-row pad `Θ` and zero elsewhere. -/
def thetaPads (p : Params) (θ : Bytes (labelBytes p)) : Pads p :=
  (fun _ => 0, θ, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ => 0, fun _ _ => 0)

/-- `u_pre` as a function of `Θ`. -/
def thetaW (p : Params) (θ : Bytes (labelBytes p)) : W128 :=
  uPreOf p (usOf p (thetaPads p θ))[0]!

lemma uPre_eq_thetaW (hlr : p.labelRows = true) (t : Pads p) :
    uPreOf p (usOf p t)[0]! = thetaW p t.2.1 := by
  have h1 : wordAt (usOf p t)[0]! p.labelRowOffset =
      wordAt (usOf p (thetaPads p t.2.1))[0]! p.labelRowOffset := wordAt_congr fun k hk => by
    rw [wbit_u0_label hlr t (by omega), wbit_u0_label hlr _ (by omega)]; rfl
  have h2 : wordAt (usOf p t)[0]! (p.labelRowOffset + 64) =
      wordAt (usOf p (thetaPads p t.2.1))[0]! (p.labelRowOffset + 64) := wordAt_congr fun k hk => by
    rw [Nat.add_assoc, wbit_u0_label hlr t (by omega), wbit_u0_label hlr _ (by omega)]; rfl
  simp only [thetaW, uPreOf, h1, h2]

lemma thetaW_bit (hlr : p.labelRows = true) (θ : Bytes (labelBytes p)) {k : ℕ} (hk : k < 128) :
    (if k < 64 then (thetaW p θ).lo.toNat.testBit k else (thetaW p θ).hi.toNat.testBit (k - 64)) =
      ((ba θ).get! (k / 8)).toNat.testBit (k % 8) := by
  unfold thetaW uPreOf
  split_ifs with h
  · rw [wordAt_testBit _ _ h, wbit_u0_label hlr _ hk]; rfl
  · rw [wordAt_testBit _ _ (by omega), Nat.add_assoc, show 64 + (k - 64) = k by omega,
      wbit_u0_label hlr _ hk]; rfl

/-- **`u_pre` determines `Θ`.** -/
lemma thetaW_injective (hlr : p.labelRows = true) : Function.Injective (thetaW p) := by
  obtain ⟨-, -, hlb, -⟩ := labelRows_sizes hlr
  intro θ θ' h
  funext j
  have hj := j.isLt
  apply UInt8.toNat_inj.1
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < 8
  · have e := thetaW_bit hlr θ (k := 8 * j + b) (by omega)
    have e' := thetaW_bit hlr θ' (k := 8 * j + b) (by omega)
    rw [h, e', show (8 * j.val + b) / 8 = j.val by omega, show (8 * j.val + b) % 8 = b by omega,
      get!_ba _ hj, get!_ba _ hj] at e
    exact e.symm
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (θ j).toNat_lt
        (Nat.pow_le_pow_right (by norm_num) (show 8 ≤ b by omega))),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (θ' j).toNat_lt
        (Nat.pow_le_pow_right (by norm_num) (show 8 ≤ b by omega)))]

end Theta

/-! ## The sibling inputs against the active ones -/

section Sib

variable (Hs : Hashes) (T : CrtTables) (st : Statement)

/-- **The sibling input of gate `e` is `iv ‖ e ‖ (L_e(q) ⊕ u_pre) ‖ 5`.** -/
lemma sibInput_eq (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows) (s : Shared)
    (t : Pads st.params) (e : Fin 312) :
    sibInput Hs T st s t e = (Prover.gateInputsOff st.params T (pubOf Hs st s (deltaOf s.2.1)).iv
      (qcolsTape Hs st s t) (uPreOf st.params (usOf st.params t)[0]!)).getD e .empty := by
  unfold sibInput
  exact siblingInput_eq st.params T hlab _ _ _ _ (qcolsOf_size st _ _ _) e.isLt

/-- The prover reads a sibling input only if `u_pre = 0`. -/
lemma uPre_zero_of_sib_mem (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    (s : Shared) (t : Pads st.params) (e : Fin 312)
    (h : sibInput Hs T st s t e ∈ actInputs Hs T st s t) :
    uPreOf st.params (usOf st.params t)[0]! = W128.zero := by
  obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.1 h
  have hl : (actInputs Hs T st s t).length = 312 := gateInputsOff_length _ _ _ _ _
  rw [sibInput_eq Hs T st hlab, ← List.getD_eq_getElem _ ByteArray.empty hi] at hie
  exact (gateInputsOff_getD_inj st.params T _ _ (e := ⟨i, by omega⟩) (e' := e) hie).2.symm

/-- The sibling input does not read the pads' sibling answers. -/
lemma sibInput_withSib (s : Shared) (u : PadsU st.params) (z z' : Sib) (e : Fin 312) :
    sibInput Hs T st s (withSib u z) e = sibInput Hs T st s (withSib u z') e := rfl

end Sib

/-! ## The bad event: a sibling input is read -/

/-- (Blocks are compared classically, for the sets of guesses.) -/
@[instance_reducible] noncomputable def decEqW128 : DecidableEq W128 := Classical.decEq _

attribute [local instance] decEqW128

lemma pr_prod_le {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] (P : α × β → Prop) {ε : ℝ}
    (h : ∀ a, pr β (fun b => P (a, b)) ≤ ε) : pr (α × β) P ≤ ε := by
  have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [pr_prod, div_le_iff₀ hα]
  calc ∑ a, pr β (fun b => P (a, b)) ≤ ∑ _a : α, ε := Finset.sum_le_sum fun a _ => h a
    _ = ε * Fintype.card α := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

section Query

variable (Hs : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)
  (cs : ByteArray → ByteArray → System GF128)

/-- The hash record with `H₅` the table `G` on the sibling inputs. -/
noncomputable abbrev H5 (G : SKey st.params → Bytes 4) : Hashes :=
  Hs.withTable .h5 (sEnc Hs T st) G

/-- **The prover's `H₅` reads, as table keys**: the keys whose input is an active gate input.
(Irreducible: unfolding it enumerates the key type.) -/
@[irreducible] noncomputable def proverKeys (x : IdealTape st.params) : Finset (SKey st.params) :=
  haveI := Classical.decPred fun k : SKey st.params => sEnc Hs T st k ∈ actInputs Hs T st x.1 x.2
  univ.filter fun k => sEnc Hs T st k ∈ actInputs Hs T st x.1 x.2

lemma mem_proverKeys {x : IdealTape st.params} {k : SKey st.params} :
    k ∈ proverKeys Hs T st x ↔ sEnc Hs T st k ∈ actInputs Hs T st x.1 x.2 := by
  unfold proverKeys; simp

lemma actInputs_withTable_h5 (G : SKey st.params → Bytes 4) (s : Shared) (t : Pads st.params) :
    actInputs (H5 Hs T st G) T st s t = actInputs Hs T st s t := by
  simp only [actInputs, qcolsTape, pubOf_withTable_h5]

/-- With `H₅` a table, the ideal-tape prover reads the table only at `proverKeys`. -/
lemma proveIdeal_table_congr (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    (x : IdealTape st.params) (G G' : SKey st.params → Bytes 4)
    (h : ∀ k ∈ proverKeys Hs T st x, G k = G' k) :
    proveIdeal (H5 Hs T st G) T st w x = proveIdeal (H5 Hs T st G') T st w x := by
  refine proveIdeal_h5_congr T st w hlab (fun k hk =>
    ((Hs.agreeOff_withTable .h5 _ G k hk).symm.trans (Hs.agreeOff_withTable .h5 _ G' k hk))) x
    fun y hy => ?_
  rw [actInputs_withTable_h5] at hy
  simp only [Hashes.withTable, ↓reduceIte]
  split
  · rename_i hy'
    have hk : hy'.choose ∈ proverKeys Hs T st x := by
      rw [mem_proverKeys, hy'.choose_spec]; exact hy
    exact congrArg ba (h _ hk)
  · rfl

/-- The ideal-tape proof from the shared tape and the fields. -/
def outOf (s : Shared) (f : SimFields st.params) : Except String ByteArray :=
  match firstHit s.2.1 with
  | none => .error "grinding failed"
  | some (ctr, delta) => .ok (simAssemble st.params s ctr delta f)

/-- The grinding outcome of a shared tape (zero if there is none). -/
def hitOf (s : Shared) : ℕ × Bytes 16 := (firstHit s.2.1).getD (0, fun _ => 0)

lemma hitOf_snd (s : Shared) : (hitOf s).2 = deltaOf s.2.1 := by
  unfold hitOf deltaOf
  rcases firstHit s.2.1 with _ | ⟨c, d⟩ <;> rfl

/-- **The ideal-tape proof is a function of the shared tape and the fields** (`fieldsOf`). -/
lemma proveIdeal_eq_outOf (Hs : Hashes) (h : ZKHyp T st w cs) (s : Shared) (t : Pads st.params) :
    proveIdeal Hs T st w (s, t) =
      outOf st s (fieldsOf Hs T st w cs s (hitOf s).1 (hitOf s).2 t).1 := by
  have hw : (w.size != st.params.witnessBytes) = false := by simp [h.hw]
  unfold proveIdeal outOf hitOf
  rw [hw]
  rcases hg : firstHit s.2.1 with _ | ⟨ctr, delta⟩
  · rfl
  · simp only [Bool.false_eq_true, ↓reduceIte, Option.getD_some]
    exact idealCore_fields Hs T st w cs h.hvals h.hdeg h.hd h.hd' h.hI h.hsat s ctr delta t

/-- The key columns `q` from the shared tape and the fields. -/
def qcolsF (s : Shared) (f : SimFields st.params) : Array (Array UInt64) :=
  qcolsOf st (pubOf Hs st s (deltaOf s.2.1)) (deltaOf s.2.1) (ba f.1)

lemma fieldsOf_corr (Hs : Hashes) (s : Shared) (ctr : ℕ) (delta : Bytes 16) (t : Pads st.params) :
    (fieldsOf Hs T st w cs s ctr delta t).1.1 = corrB t := rfl

lemma qcolsTape_eq_qcolsF (Hs' : Hashes) (s : Shared) (ctr : ℕ) (delta : Bytes 16)
    (t : Pads st.params) :
    qcolsTape Hs st s t = qcolsF Hs st s (fieldsOf Hs' T st w cs s ctr delta t).1 := by
  rw [qcolsTape, qcolsF, fieldsOf_corr, correctionsOf_eq]

/-- **The guess of a query** `k`: the offset `v` (if any) that makes `k`'s input a gate input
`iv ‖ e ‖ (L_e(q) ⊕ v) ‖ 5`. It is unique (`gateInputsOff_getD_inj`) and a function of the
shared tape and the fields. -/
noncomputable def guessOf (s : Shared) (f : SimFields st.params) (k : SKey st.params) :
    Finset W128 :=
  haveI := Classical.propDecidable
  if h : ∃ v : W128, ∃ e : Fin 312, sEnc Hs T st k = (Prover.gateInputsOff st.params T
      (pubOf Hs st s (deltaOf s.2.1)).iv (qcolsF Hs st s f) v).getD e .empty then {h.choose}
  else ∅

lemma card_guessOf_le (s : Shared) (f : SimFields st.params) (k : SKey st.params) :
    (guessOf Hs T st s f k).card ≤ 1 := by
  unfold guessOf; split <;> simp

lemma mem_guessOf {s : Shared} {f : SimFields st.params} {k : SKey st.params} {v : W128}
    {e : Fin 312} (h : sEnc Hs T st k = (Prover.gateInputsOff st.params T
      (pubOf Hs st s (deltaOf s.2.1)).iv (qcolsF Hs st s f) v).getD e .empty) :
    v ∈ guessOf Hs T st s f k := by
  have hex : ∃ v : W128, ∃ e : Fin 312, sEnc Hs T st k = (Prover.gateInputsOff st.params T
      (pubOf Hs st s (deltaOf s.2.1)).iv (qcolsF Hs st s f) v).getD e .empty := ⟨v, e, h⟩
  unfold guessOf
  rw [dite_eq_left_of_eq_true (eq_true hex), Finset.mem_singleton]
  obtain ⟨e', he'⟩ := hex.choose_spec
  exact (gateInputsOff_getD_inj st.params T _ _ (h.symm.trans he')).2

variable (QD : Except String ByteArray → (SKey st.params → Bytes 4) → Finset (SKey st.params))

/-- **The candidates for `u_pre`**: zero (the prover's own reads) and the queries' guesses. -/
noncomputable def guesses (G : SKey st.params → Bytes 4) (s : Shared) (f : SimFields st.params) :
    Finset W128 :=
  insert W128.zero ((QD (outOf st s f) G).biUnion (guessOf Hs T st s f))

lemma card_guesses_le {q : ℕ} (hq : ∀ o G, (QD o G).card ≤ q) (G : SKey st.params → Bytes 4)
    (s : Shared) (f : SimFields st.params) : (guesses Hs T st QD G s f).card ≤ q + 1 := by
  unfold guesses
  refine (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ?_)
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ k ∈ QD (outOf st s f) G, (guessOf Hs T st s f k).card
      ≤ ∑ _k ∈ QD (outOf st s f) G, 1 := Finset.sum_le_sum fun k _ => card_guessOf_le Hs T st s f k
    _ ≤ q := by rw [Finset.sum_const, smul_eq_mul, mul_one]; exact hq _ _

/-- **A sibling input read by the prover or by `D` is a correct guess of `u_pre`.** -/
lemma bad_mem_guesses (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    (h : ZKHyp T st w cs) (G : SKey st.params → Bytes 4) (s : Shared) (t : Pads st.params)
    (hbad : ∃ e, sibKey Hs T st (s, dropSib t) e ∈ proverKeys Hs T st (s, t) ∪
      QD (proveIdeal (H5 Hs T st G) T st w (s, t)) G) :
    uPreOf st.params (usOf st.params t)[0]! ∈ guesses Hs T st QD G s
      (fieldsOf (H5 Hs T st G) T st w cs s (hitOf s).1 (hitOf s).2 t).1 := by
  obtain ⟨e, he⟩ := hbad
  have hsib : sEnc Hs T st (sibKey Hs T st (s, dropSib t) e) = sibInput Hs T st s t e := by
    rw [sibKey, enc_keyOf (sEnc Hs T st)]; rfl
  rw [Finset.mem_union] at he
  unfold guesses
  rw [Finset.mem_insert]
  rcases he with he | he
  · left
    rw [mem_proverKeys, hsib] at he
    exact uPre_zero_of_sib_mem Hs T st hlab s t e he
  · right
    rw [Finset.mem_biUnion]
    refine ⟨_, by rw [← proveIdeal_eq_outOf T st w cs _ h]; exact he, mem_guessOf Hs T st (e := e) ?_⟩
    rw [hsib, sibInput_eq Hs T st hlab, qcolsTape_eq_qcolsF]

lemma fieldsOf_theta (Hs : Hashes) (s : Shared) (ctr : ℕ) (delta : Bytes 16) (t : Pads st.params) :
    (fieldsOf Hs T st w cs s ctr delta t).2 = t.2.1 := rfl

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024 in
/-- **For a fixed shared tape and table, a sibling input is read with probability
`≤ (q + 1)·2⁻¹²⁸`**: by the prover (`u_pre = 0`) or by one of `D`'s `q` queries (each a guess of
`u_pre` from the proof). `Θ` is uniform given the fields (`upush_fieldsOf`). -/
theorem pr_bad_le (hlr : st.params.labelRows = true) (h : ZKHyp T st w cs) {q : ℕ}
    (hq : ∀ o G, (QD o G).card ≤ q) (G : SKey st.params → Bytes 4) (s : Shared) :
    pr (Pads st.params) (fun t => ∃ e, sibKey Hs T st (s, dropSib t) e ∈
      proverKeys Hs T st (s, t) ∪ QD (proveIdeal (H5 Hs T st G) T st w (s, t)) G) ≤
      (q + 1) / 2 ^ 128 := by
  obtain ⟨h1, -, hlb, h2⟩ := labelRows_sizes hlr
  have hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows := by omega
  let F := fieldsOf (H5 Hs T st G) T st w cs s (hitOf s).1 (hitOf s).2
  let S := guesses Hs T st QD G s
  have e1 : pr (Pads st.params) (fun t => ∃ e, sibKey Hs T st (s, dropSib t) e ∈
      proverKeys Hs T st (s, t) ∪ QD (proveIdeal (H5 Hs T st G) T st w (s, t)) G) ≤
      pr (Pads st.params) (fun t => thetaW st.params (F t).2 ∈ S (F t).1) :=
    pr_mono fun t ht => by
      have hm := bad_mem_guesses Hs T st w cs QD hlab h G s t ht
      rw [uPre_eq_thetaW hlr] at hm
      rw [fieldsOf_theta]
      exact hm
  have e2 : pr (Pads st.params) (fun t => thetaW st.params (F t).2 ∈ S (F t).1) =
      pr (SimFields st.params × Bytes (labelBytes st.params))
        (fun y => thetaW st.params y.2 ∈ S y.1) := by
    have := (upush_fieldsOf (H5 Hs T st G) T st w cs s (hitOf s).1 (hitOf s).2 h.hT h.hnm)
      (fun y => thetaW st.params y.2 ∈ S y.1)
    rw [abs_nonpos_iff, sub_eq_zero] at this
    exact this
  have e3 : pr (SimFields st.params × Bytes (labelBytes st.params))
      (fun y => thetaW st.params y.2 ∈ S y.1) ≤
      ((q + 1 : ℕ) : ℝ) / Fintype.card (Bytes (labelBytes st.params)) := by
    rw [← pr_equiv (Equiv.prodComm (Bytes (labelBytes st.params)) (SimFields st.params))]
    exact pr_mem_indep_le (thetaW st.params) (thetaW_injective hlr) S
      (card_guesses_le Hs T st QD hq G s)
  have hc : ((2 ^ (8 * labelBytes st.params) : ℕ) : ℝ) = 2 ^ 128 := by rw [hlb]; norm_num
  rw [Prob.card_bytes, hc] at e3
  refine (e1.trans (e2.le.trans e3)).trans (le_of_eq ?_)
  push_cast
  norm_num

set_option synthInstance.maxSize 1024 in
/-- **H6 in the ROM against a distinguisher that reads `H₅` at `q` keys**: with `H₅` a uniform
table on the sibling inputs and dedicated label rows, the hop of `LabHyp` (the ideal-tape prover
with the sibling answers recomputed from the table, against uniform ones) costs at most
`(q + 1)·2⁻¹²⁸` for every distinguisher `D` of the proof and the table that reads the table only at
the (at most `q`) keys `QD` (`hQD`; chosen adaptively, as functions of the proof and the table). -/
theorem lab_rom_query (hlr : st.params.labelRows = true) (h : ZKHyp T st w cs)
    (D : Except String ByteArray → (SKey st.params → Bytes 4) → Prop)
    (hQD : ∀ o G G', (∀ k ∈ QD o G, G k = G' k) → (D o G ↔ D o G')) {q : ℕ}
    (hq : ∀ o G, (QD o G).card ≤ q) :
    |pr ((Shared × PadsU st.params) × (SKey st.params → Bytes 4)) (fun x =>
        D (proveIdeal (H5 Hs T st x.2) T st w (fillSib (H5 Hs T st x.2) T st
          (x.1.1, withSib x.1.2 fun _ => fun _ => 0))) x.2) -
      pr ((Shared × PadsU st.params) × ((SKey st.params → Bytes 4) × Sib))
        (fun x => D (proveIdeal (H5 Hs T st x.2.1) T st w (x.1.1, withSib x.1.2 x.2.2)) x.2.1)| ≤
      (q + 1) / 2 ^ 128 := by
  obtain ⟨h1, -, -, h2⟩ := labelRows_sizes hlr
  have hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows := by omega
  refine (lab_rom Hs T st (fun t G => D (proveIdeal (H5 Hs T st G) T st w t) G)
    (fun t G => proverKeys Hs T st t ∪ QD (proveIdeal (H5 Hs T st G) T st w t) G)
    fun t G G' hG => ?_).trans ?_
  · have hp := proveIdeal_table_congr Hs T st w hlab t G G' fun k hk =>
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
    rw [← pr_equiv E]
    refine pr_prod_le _ fun G => pr_prod_le _ fun s => ?_
    exact pr_bad_le Hs T st w cs QD hlr h hq G s

lemma fillSib_withSib (Hs : Hashes) (s : Shared) (u : PadsU st.params) (z z' : Sib) :
    fillSib Hs T st (s, withSib u z) = fillSib Hs T st (s, withSib u z') := by
  have e : ∀ z, fillSib Hs T st (s, withSib u z) =
      (s, withSib u (sibOf Hs T st s (withSib u z))) := fun _ => rfl
  rw [e, e, sibOf_withSib' Hs T st s u z z']

set_option synthInstance.maxSize 1024 in
/-- **`LabHyp` in the ROM** (`lab_rom_query` on the tape): on a uniform tape and a uniform `H₅`
table on the sibling inputs, the ideal-tape prover with the sibling answers its tape determines
(`fillSib`, recomputed from the table) and the one with uniform sibling answers are
`(q + 1)·2⁻¹²⁸`-close, against every distinguisher that also reads the table at `q` keys. -/
theorem lab_rom_hyp (hlr : st.params.labelRows = true) (h : ZKHyp T st w cs)
    (D : Except String ByteArray → (SKey st.params → Bytes 4) → Prop)
    (hQD : ∀ o G G', (∀ k ∈ QD o G, G k = G' k) → (D o G ↔ D o G')) {q : ℕ}
    (hq : ∀ o G, (QD o G).card ≤ q) :
    |pr (IdealTape st.params × (SKey st.params → Bytes 4)) (fun x =>
        D (proveIdeal (H5 Hs T st x.2) T st w (fillSib (H5 Hs T st x.2) T st x.1)) x.2) -
      pr (IdealTape st.params × (SKey st.params → Bytes 4))
        (fun x => D (proveIdeal (H5 Hs T st x.2) T st w x.1) x.2)| ≤ (q + 1) / 2 ^ 128 := by
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
  exact lab_rom_query Hs T st w cs QD hlr h D hQD hq

end Query

/-! ## H6 for any table layout of `H₅`

The same argument for a table on any key type `K` with inputs `enc`, given the key `sk c e` of
the sibling input of gate `e` of every tape `c` (`hsk`, and `keyOf enc` fixing it, `hkey`): the
layout of the sections above (keys a tape and a gate, `sEnc`) and a table on every `37`-byte
input (`ZK/HopsH23.lean`) are instances. -/

section QueryG

variable (Hs : Hashes) (T : CrtTables) (st : Statement) (w : ByteArray)
  (cs : ByteArray → ByteArray → System GF128)
  {K : Type} [Fintype K] [DecidableEq K] (enc : K → ByteArray)
  (sk : Shared × PadsU st.params → Fin 312 → K)

lemma skG_injective
    (hsk : ∀ c e, enc (sk c e) = sibInput Hs T st c.1 (withSib c.2 fun _ => fun _ => 0) e)
    (c : Shared × PadsU st.params) : Function.Injective (sk c) := by
  intro e e' h
  have h1 := congrArg enc h
  rw [hsk, hsk] at h1
  have h2 := congrArg (fun b => AES.getLE32 b (pubOf Hs st c.1 (deltaOf c.1.2.1)).iv.size) h1
  simp only [getLE32_sibInput] at h2
  have h3 := congrArg UInt32.toNat h2
  rw [toNat_toUInt32 (by have := e.isLt; omega), toNat_toUInt32 (by have := e'.isLt; omega)] at h3
  exact Fin.ext h3

lemma fillSib_withTableG
    (hsk : ∀ c e, enc (sk c e) = sibInput Hs T st c.1 (withSib c.2 fun _ => fun _ => 0) e)
    (hkey : ∀ c e, keyOf enc (sk c e) = sk c e) (G : K → Bytes 4) (c : Shared × PadsU st.params)
    (z : Sib) :
    fillSib (Hs.withTable .h5 enc G) T st (c.1, withSib c.2 z) = (c.1, withSib c.2 (G ∘ sk c)) := by
  have e1 : fillSib (Hs.withTable .h5 enc G) T st (c.1, withSib c.2 z) =
      (c.1, withSib c.2 (sibOf (Hs.withTable .h5 enc G) T st c.1 (withSib c.2 z))) := rfl
  rw [e1, sibOf_withSib' _ T st c.1 c.2 z fun _ => fun _ => 0, sibOf_withTable]
  congr 2
  funext e
  have h := Hashes.withTable_enc Hs .h5 enc G (sk c e)
  rw [← hsk c e, h, hkey]
  exact blk_ba (n := 4) _

set_option synthInstance.maxSize 1024 in
/-- `lab_rom` for any layout. -/
theorem lab_romG
    (hsk : ∀ c e, enc (sk c e) = sibInput Hs T st c.1 (withSib c.2 fun _ => fun _ => 0) e)
    (hkey : ∀ c e, keyOf enc (sk c e) = sk c e)
    (A : IdealTape st.params → (K → Bytes 4) → Prop)
    (Q : IdealTape st.params → (K → Bytes 4) → Finset K)
    (hQ : ∀ t G G', (∀ k ∈ Q t G, G k = G' k) → (A t G ↔ A t G')) :
    |pr ((Shared × PadsU st.params) × (K → Bytes 4)) (fun x =>
        A (fillSib (Hs.withTable .h5 enc x.2) T st
          (x.1.1, withSib x.1.2 fun _ => fun _ => 0)) x.2) -
      pr ((Shared × PadsU st.params) × ((K → Bytes 4) × Sib))
        (fun x => A (x.1.1, withSib x.1.2 x.2.2) x.2.1)| ≤
      pr ((Shared × PadsU st.params) × ((K → Bytes 4) × Sib))
        (fun x => ∃ e, sk x.1 e ∈ Q (x.1.1, withSib x.1.2 x.2.2) x.2.1) := by
  simp only [fillSib_withTableG Hs T st enc sk hsk hkey]
  exact abs_pr_hidden_le (skG_injective Hs T st enc sk hsk) (fun c u G => A (c.1, withSib c.2 u) G)
    (fun c u G => Q (c.1, withSib c.2 u) G) fun c u G G' h => hQ _ G G' h

/-- **The prover's `H₅` reads, as table keys** (any layout). -/
@[irreducible] noncomputable def proverKeysG (x : IdealTape st.params) : Finset K :=
  haveI := Classical.decPred fun k : K => enc k ∈ actInputs Hs T st x.1 x.2
  univ.filter fun k => enc k ∈ actInputs Hs T st x.1 x.2

lemma mem_proverKeysG {x : IdealTape st.params} {k : K} :
    k ∈ proverKeysG Hs T st enc x ↔ enc k ∈ actInputs Hs T st x.1 x.2 := by
  unfold proverKeysG; simp

lemma actInputs_withTable_h5G (G : K → Bytes 4) (s : Shared) (t : Pads st.params) :
    actInputs (Hs.withTable .h5 enc G) T st s t = actInputs Hs T st s t := by
  simp only [actInputs, qcolsTape, pubOf_withTable_h5]

/-- With `H₅` a table, the ideal-tape prover reads the table only at `proverKeysG`. -/
lemma proveIdeal_table_congrG (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    (x : IdealTape st.params) (G G' : K → Bytes 4)
    (h : ∀ k ∈ proverKeysG Hs T st enc x, G k = G' k) :
    proveIdeal (Hs.withTable .h5 enc G) T st w x = proveIdeal (Hs.withTable .h5 enc G') T st w x := by
  refine proveIdeal_h5_congr T st w hlab (fun k hk =>
    ((Hs.agreeOff_withTable .h5 _ G k hk).symm.trans (Hs.agreeOff_withTable .h5 _ G' k hk))) x
    fun y hy => ?_
  rw [actInputs_withTable_h5G] at hy
  simp only [Hashes.withTable, ↓reduceIte]
  split
  · rename_i hy'
    have hk : hy'.choose ∈ proverKeysG Hs T st enc x := by
      rw [mem_proverKeysG, hy'.choose_spec]; exact hy
    exact congrArg ba (h _ hk)
  · rfl

/-- The guess of a query (any layout). -/
noncomputable def guessOfG (s : Shared) (f : SimFields st.params) (k : K) : Finset W128 :=
  haveI := Classical.propDecidable
  if h : ∃ v : W128, ∃ e : Fin 312, enc k = (Prover.gateInputsOff st.params T
      (pubOf Hs st s (deltaOf s.2.1)).iv (qcolsF Hs st s f) v).getD e .empty then {h.choose}
  else ∅

lemma card_guessOfG_le (s : Shared) (f : SimFields st.params) (k : K) :
    (guessOfG Hs T st enc s f k).card ≤ 1 := by
  unfold guessOfG; split <;> simp

lemma mem_guessOfG {s : Shared} {f : SimFields st.params} {k : K} {v : W128}
    {e : Fin 312} (h : enc k = (Prover.gateInputsOff st.params T
      (pubOf Hs st s (deltaOf s.2.1)).iv (qcolsF Hs st s f) v).getD e .empty) :
    v ∈ guessOfG Hs T st enc s f k := by
  have hex : ∃ v : W128, ∃ e : Fin 312, enc k = (Prover.gateInputsOff st.params T
      (pubOf Hs st s (deltaOf s.2.1)).iv (qcolsF Hs st s f) v).getD e .empty := ⟨v, e, h⟩
  unfold guessOfG
  rw [dite_eq_left_of_eq_true (eq_true hex), Finset.mem_singleton]
  obtain ⟨e', he'⟩ := hex.choose_spec
  exact (gateInputsOff_getD_inj st.params T _ _ (h.symm.trans he')).2

variable (QD : Except String ByteArray → (K → Bytes 4) → Finset K)

/-- The candidates for `u_pre` (any layout). -/
noncomputable def guessesG (G : K → Bytes 4) (s : Shared) (f : SimFields st.params) :
    Finset W128 :=
  insert W128.zero ((QD (outOf st s f) G).biUnion (guessOfG Hs T st enc s f))

lemma card_guessesG_le {q : ℕ} (hq : ∀ o G, (QD o G).card ≤ q) (G : K → Bytes 4)
    (s : Shared) (f : SimFields st.params) : (guessesG Hs T st enc QD G s f).card ≤ q + 1 := by
  unfold guessesG
  refine (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ?_)
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ k ∈ QD (outOf st s f) G, (guessOfG Hs T st enc s f k).card
      ≤ ∑ _k ∈ QD (outOf st s f) G, 1 :=
        Finset.sum_le_sum fun k _ => card_guessOfG_le Hs T st enc s f k
    _ ≤ q := by rw [Finset.sum_const, smul_eq_mul, mul_one]; exact hq _ _

lemma bad_mem_guessesG
    (hsk : ∀ c e, enc (sk c e) = sibInput Hs T st c.1 (withSib c.2 fun _ => fun _ => 0) e)
    (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    (h : ZKHyp T st w cs) (G : K → Bytes 4) (s : Shared) (t : Pads st.params)
    (hbad : ∃ e, sk (s, dropSib t) e ∈ proverKeysG Hs T st enc (s, t) ∪
      QD (proveIdeal (Hs.withTable .h5 enc G) T st w (s, t)) G) :
    uPreOf st.params (usOf st.params t)[0]! ∈ guessesG Hs T st enc QD G s
      (fieldsOf (Hs.withTable .h5 enc G) T st w cs s (hitOf s).1 (hitOf s).2 t).1 := by
  obtain ⟨e, he⟩ := hbad
  have hsib : enc (sk (s, dropSib t) e) = sibInput Hs T st s t e := by
    rw [hsk]; rfl
  rw [Finset.mem_union] at he
  unfold guessesG
  rw [Finset.mem_insert]
  rcases he with he | he
  · left
    rw [mem_proverKeysG, hsib] at he
    exact uPre_zero_of_sib_mem Hs T st hlab s t e he
  · right
    rw [Finset.mem_biUnion]
    refine ⟨_, by rw [← proveIdeal_eq_outOf T st w cs _ h]; exact he,
      mem_guessOfG Hs T st enc (e := e) ?_⟩
    rw [hsib, sibInput_eq Hs T st hlab, qcolsTape_eq_qcolsF]

set_option synthInstance.maxSize 1024 in
/-- `pr_bad_le` for any layout. -/
theorem pr_bad_leG
    (hsk : ∀ c e, enc (sk c e) = sibInput Hs T st c.1 (withSib c.2 fun _ => fun _ => 0) e)
    (hlr : st.params.labelRows = true) (h : ZKHyp T st w cs) {q : ℕ}
    (hq : ∀ o G, (QD o G).card ≤ q) (G : K → Bytes 4) (s : Shared) :
    pr (Pads st.params) (fun t => ∃ e, sk (s, dropSib t) e ∈
      proverKeysG Hs T st enc (s, t) ∪ QD (proveIdeal (Hs.withTable .h5 enc G) T st w (s, t)) G) ≤
      (q + 1) / 2 ^ 128 := by
  obtain ⟨h1, -, hlb, h2⟩ := labelRows_sizes hlr
  have hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows := by omega
  let F := fieldsOf (Hs.withTable .h5 enc G) T st w cs s (hitOf s).1 (hitOf s).2
  let S := guessesG Hs T st enc QD G s
  have e1 : pr (Pads st.params) (fun t => ∃ e, sk (s, dropSib t) e ∈
      proverKeysG Hs T st enc (s, t) ∪ QD (proveIdeal (Hs.withTable .h5 enc G) T st w (s, t)) G) ≤
      pr (Pads st.params) (fun t => thetaW st.params (F t).2 ∈ S (F t).1) :=
    pr_mono fun t ht => by
      have hm := bad_mem_guessesG Hs T st w cs enc sk QD hsk hlab h G s t ht
      rw [uPre_eq_thetaW hlr] at hm
      rw [fieldsOf_theta]
      exact hm
  have e2 : pr (Pads st.params) (fun t => thetaW st.params (F t).2 ∈ S (F t).1) =
      pr (SimFields st.params × Bytes (labelBytes st.params))
        (fun y => thetaW st.params y.2 ∈ S y.1) := by
    have := (upush_fieldsOf (Hs.withTable .h5 enc G) T st w cs s (hitOf s).1 (hitOf s).2 h.hT
      h.hnm) (fun y => thetaW st.params y.2 ∈ S y.1)
    rw [abs_nonpos_iff, sub_eq_zero] at this
    exact this
  have e3 : pr (SimFields st.params × Bytes (labelBytes st.params))
      (fun y => thetaW st.params y.2 ∈ S y.1) ≤
      ((q + 1 : ℕ) : ℝ) / Fintype.card (Bytes (labelBytes st.params)) := by
    rw [← pr_equiv (Equiv.prodComm (Bytes (labelBytes st.params)) (SimFields st.params))]
    exact pr_mem_indep_le (thetaW st.params) (thetaW_injective hlr) S
      (card_guessesG_le Hs T st enc QD hq G s)
  have hc : ((2 ^ (8 * labelBytes st.params) : ℕ) : ℝ) = 2 ^ 128 := by rw [hlb]; norm_num
  rw [Prob.card_bytes, hc] at e3
  refine (e1.trans (e2.le.trans e3)).trans (le_of_eq ?_)
  push_cast
  norm_num

end QueryG

end VoleMole.ZK.Sim
