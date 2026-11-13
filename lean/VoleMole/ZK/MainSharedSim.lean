import VoleMole.ZK.MainSharedGame
import VoleMole.ZK.MainPU

/-!
# The bad event of the shared-table joint hop on simulated proofs (`lean/docs/zk.md` §4.2)

`main_shared_le` (`ZK/MainSharedGame.lean`) leaves `Pr[bstar]` in the game with all proofs
simulated. Here are the generic steps that turn it into a prediction of the witness prefixes and
explicit collision terms, for one simulated proof with coins `c` and statement `st`.

* `actL`, `sibL r`: the verifier's gate inputs of the simulated proof (the active labels), and the
  same at the label offset `thetaMain d[0..16) r` (the sibling labels if the witness prefix is
  `r`); `zeroC r`: that offset is zero; `errC`: the simulation failed. The slot predicates of
  `bstar` on a simulated proof are these (`slotHit_sim`, `slotKeys_sim`, `slotZero_sim`,
  `slotErr_sim`).
* **`candC`**: the candidates for the witness prefix from a set `S` of `H₅` keys: `r` with
  `zeroC r` or with a key of `S` among `sibL r`. It reads the simulated proof, the statement and
  `S`: nothing of the witness. **`card_candC_le`**: at most `|S| + 1` candidates.
* **`pr_sib_hit_le`** (item (iii) of `lean/docs/zk.md` §4.2): for any list `tg` of at most `N` byte
  strings that does not depend on the simulator's field `d`, the probability over a uniform `d`
  that some string of `tg` is among `sibL r` is at most `(N + 1)·2⁻¹²⁸`, whatever `r`. This bounds
  the event that a gate input of one simulated proof is a sibling gate input of another: the later
  proof's `d` is uniform and independent of the earlier proofs. No property of `H₄` or of the `iv`
  is used.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy
  VoleMole.ZK.IC
open VoleMole.Privacy.MainChain

attribute [local instance] decEqW128
attribute [local irreducible] simulate

/-! ## The verifier's gate inputs: length and size -/

section VIn

variable [HasPrg] (Hs : Hashes) (T : CrtTables) (st : Statement)

lemma vInOff_length_le (proof : ByteArray) (off : W128) :
    (vInOff Hs T st proof off).length ≤ 312 := by
  unfold vInOff
  dsimp only
  split
  · simp
  · rw [gateInputsOff_length]

/-- **A gate input has `37` bytes.** -/
lemma vInOff_size (hHs : HashesWF Hs) (proof : ByteArray) (off : W128) {x : ByteArray}
    (hx : x ∈ vInOff Hs T st proof off) : x.size = 37 := by
  unfold vInOff at hx
  dsimp only at hx
  split at hx
  · simp at hx
  · obtain ⟨e, he, rfl⟩ := List.mem_iff_getElem.1 hx
    have he' : e < 312 := by rw [gateInputsOff_length] at he; exact he
    have hiv : (ivOf Hs ⟨st.params, proof⟩ (st.mu1 Hs)).size = 16 := hHs .h4 _
    rw [← List.getD_eq_getElem _ ByteArray.empty he, gateInputsOff_getD st.params T _ _ _ he',
      ByteArray.size_push, ByteArray.size_append, size_pushLE32, W128.toBytes_size, hiv]

end VIn

/-! ## One simulated proof -/

section Sim

variable (Hb : Hashes) (p : Params)

/-- The simulation failed. -/
def errC (c : SimCoins p) : Prop := ∃ e, simulate p c = .error e

/-- **The active gate inputs of a simulated proof** (the verifier's). -/
noncomputable def actL (st : Statement) (E : Cipher) (c : SimCoins p) : List ByteArray :=
  match simulate p c with
  | .ok b => @vInOff (icPrg E) Hb CrtGen.tables (withP st p) b W128.zero
  | .error _ => []

/-- **The sibling gate inputs of a simulated proof, if its witness prefix is `r`**: the gate
inputs at the label offset `thetaMain d[0..16) r`. -/
noncomputable def sibL (st : Statement) (E : Cipher) (c : SimCoins p) (r : Bytes 16) :
    List ByteArray :=
  match simulate p c with
  | .ok b => @vInOff (icPrg E) Hb CrtGen.tables (withP st p) b (thetaMain (dPre p b) r)
  | .error _ => []

/-- The label offset `thetaMain d[0..16) r` of a simulated proof is zero. -/
def zeroC (c : SimCoins p) (r : Bytes 16) : Prop :=
  match simulate p c with
  | .ok b => thetaMain (dPre p b) r = W128.zero
  | .error _ => False

variable {p}

lemma slotErr_sim (c : SimCoins p) : slotErr (some (simulate p c)) ↔ errC p c := by
  unfold slotErr errC
  simp

lemma slotZero_sim (y : SW) (c : SimCoins p) :
    slotZero p (some y) (some (simulate p c)) ↔ zeroC p c (wPre y.2) := by
  unfold slotZero zeroC
  rcases simulate p c with e | b <;> exact Iff.rfl

lemma slotHit_sim (y : SW) (c : SimCoins p) (E : Cipher) (k : Bytes 37) :
    slotHit Hb p (some y) (some (simulate p c)) E k ↔ enc5 k ∈ sibL Hb p y.1 E c (wPre y.2) := by
  unfold slotHit sibL
  rcases simulate p c with e | b
  · simp
  · exact Iff.rfl

lemma slotKeys_sim (y : SW) (c : SimCoins p) (E : Cipher) :
    slotKeys Hb p (some y) (some (simulate p c)) E =
      (actL Hb p y.1 E c).toFinset.image (blk 37) ∪
        (sibL Hb p y.1 E c (wPre y.2)).toFinset.image (blk 37) := by
  classical
  unfold slotKeys actL sibL
  rcases simulate p c with e | b
  · simp
  · simp only [proofKeys, image_union]

lemma actL_length_le (st : Statement) (E : Cipher) (c : SimCoins p) :
    (actL Hb p st E c).length ≤ 312 := by
  unfold actL
  split
  · exact @vInOff_length_le (icPrg E) _ _ _ _ _
  · simp

lemma sibL_length_le (st : Statement) (E : Cipher) (c : SimCoins p) (r : Bytes 16) :
    (sibL Hb p st E c r).length ≤ 312 := by
  unfold sibL
  split
  · exact @vInOff_length_le (icPrg E) _ _ _ _ _
  · simp

lemma actL_size (hHb : HashesWF Hb) (st : Statement) (E : Cipher) (c : SimCoins p) {x : ByteArray}
    (hx : x ∈ actL Hb p st E c) : x.size = 37 := by
  unfold actL at hx
  split at hx
  · exact @vInOff_size (icPrg E) _ _ _ hHb _ _ _ hx
  · simp at hx

lemma sibL_size (hHb : HashesWF Hb) (st : Statement) (E : Cipher) (c : SimCoins p) (r : Bytes 16)
    {x : ByteArray} (hx : x ∈ sibL Hb p st E c r) : x.size = 37 := by
  unfold sibL at hx
  split at hx
  · exact @vInOff_size (icPrg E) _ _ _ hHb _ _ _ hx
  · simp at hx

/-- **The sibling inputs of a simulated proof, on the coins**: the gate inputs at the simulator's
`iv` and key columns, at the offset `thetaMain d[0..16) r` with `d` the simulator's field. Only
the offset depends on `d`. -/
lemma sibL_coins (hm : MainP p) (st : Statement) (E : Cipher) (c : SimCoins p) (r : Bytes 16)
    {ctr : ℕ} {δ : Bytes 16} (hf : firstHit c.1.2.1 = some (ctr, δ)) :
    sibL Hb p st E c r = Prover.gateInputsOff p CrtGen.tables
      (@pubOf (icPrg E) Hb (withP st p) c.1 δ).iv
      (@qcolsOf (icPrg E) (withP st p) (@pubOf (icPrg E) Hb (withP st p) c.1 δ) δ (ba c.2.1))
      (thetaMain (pre16 hm.hw c.2.2.2.2.1) r) := by
  have ho : simulate p c = .ok (simAssemble p c.1 ctr δ c.2) := by
    unfold simulate
    rw [hf]
    rfl
  unfold sibL
  rw [ho]
  dsimp only
  rw [dPre_simAssemble hm.hw]
  exact @vInOff_simAssemble (icPrg E) Hb CrtGen.tables (withP st p) c.1 ctr δ c.2 hf _

lemma sibL_of_none (st : Statement) (E : Cipher) (c : SimCoins p) (r : Bytes 16)
    (hf : firstHit c.1.2.1 = none) : sibL Hb p st E c r = [] := by
  have ho : simulate p c = .error "grinding failed" := by
    unfold simulate
    rw [hf]
  unfold sibL
  rw [ho]

/-! ## The candidates -/

/-- **The candidates for the witness prefix of a simulated proof** from a set `S` of `H₅` keys:
the `r` whose label offset is zero, or for which a key of `S` is a sibling gate input. -/
noncomputable def candC (st : Statement) (E : Cipher) (c : SimCoins p) (S : Finset (Bytes 37)) :
    Finset (Bytes 16) :=
  haveI := Classical.decPred fun r : Bytes 16 =>
    zeroC p c r ∨ ∃ k ∈ S, enc5 k ∈ sibL Hb p st E c r
  univ.filter fun r => zeroC p c r ∨ ∃ k ∈ S, enc5 k ∈ sibL Hb p st E c r

lemma mem_candC {st : Statement} {E : Cipher} {c : SimCoins p} {S : Finset (Bytes 37)}
    {r : Bytes 16} :
    r ∈ candC Hb st E c S ↔ zeroC p c r ∨ ∃ k ∈ S, enc5 k ∈ sibL Hb p st E c r := by
  unfold candC
  simp

lemma candC_mono {st : Statement} {E : Cipher} {c : SimCoins p} {S S' : Finset (Bytes 37)}
    (h : S ⊆ S') : candC Hb st E c S ⊆ candC Hb st E c S' := by
  intro r hr
  rw [mem_candC] at hr ⊢
  rcases hr with hr | ⟨k, hk, hx⟩
  · exact Or.inl hr
  · exact Or.inr ⟨k, h hk, hx⟩

/-- A byte string is a gate input at one offset at most. -/
lemma gateInputsOff_off_unique (T : CrtTables) (iv : ByteArray) (q : Array (Array UInt64))
    {v v' : W128} {x : ByteArray} (h : x ∈ Prover.gateInputsOff p T iv q v)
    (h' : x ∈ Prover.gateInputsOff p T iv q v') : v = v' := by
  obtain ⟨e, he, hxe⟩ := List.mem_iff_getElem.1 h
  obtain ⟨e', he', hxe'⟩ := List.mem_iff_getElem.1 h'
  rw [gateInputsOff_length] at he he'
  rw [← List.getD_eq_getElem _ ByteArray.empty (by rw [gateInputsOff_length]; exact he)] at hxe
  rw [← List.getD_eq_getElem _ ByteArray.empty (by rw [gateInputsOff_length]; exact he')] at hxe'
  exact (gateInputsOff_getD_inj p T iv q (e := ⟨e, he⟩) (e' := ⟨e', he'⟩)
    (hxe.trans hxe'.symm)).2

/-- **At most `|S| + 1` candidates.** -/
theorem card_candC_le (hm : MainP p) (st : Statement) (E : Cipher) (c : SimCoins p)
    (S : Finset (Bytes 37)) : (candC Hb st E c S).card ≤ S.card + 1 := by
  classical
  rcases hf : firstHit c.1.2.1 with _ | ⟨ctr, δ⟩
  · -- no proof: no candidate
    have : candC Hb st E c S = ∅ := by
      ext r
      rw [mem_candC]
      have ho : simulate p c = .error "grinding failed" := by
        unfold simulate
        rw [hf]
      simp [zeroC, ho, sibL_of_none Hb st E c r hf]
    rw [this]; simp
  · have ho : simulate p c = .ok (simAssemble p c.1 ctr δ c.2) := by
      unfold simulate
      rw [hf]
      rfl
    -- every candidate is the zero candidate or is named by a key
    let Z : Finset (Bytes 16) := univ.filter fun r => thetaMain (pre16 hm.hw c.2.2.2.2.1) r = W128.zero
    let K : Bytes 37 → Finset (Bytes 16) := fun k =>
      univ.filter fun r => enc5 k ∈ sibL Hb p st E c r
    have hsub : candC Hb st E c S ⊆ Z ∪ S.biUnion K := by
      intro r hr
      rw [mem_candC] at hr
      rw [mem_union, mem_biUnion]
      rcases hr with hr | ⟨k, hk, hx⟩
      · left
        unfold zeroC at hr
        rw [ho] at hr
        simp only [Z, mem_filter, mem_univ, true_and]
        rw [← dPre_simAssemble hm.hw c.1 ctr δ c.2]
        exact hr
      · exact Or.inr ⟨k, hk, by simp only [K, mem_filter, mem_univ, true_and]; exact hx⟩
    have hZ : Z.card ≤ 1 := by
      refine Finset.card_le_one.2 fun r hr r' hr' => ?_
      simp only [Z, mem_filter, mem_univ, true_and] at hr hr'
      exact thetaMain_injective _ (hr.trans hr'.symm)
    have hK : ∀ k, (K k).card ≤ 1 := by
      intro k
      refine Finset.card_le_one.2 fun r hr r' hr' => ?_
      simp only [K, mem_filter, mem_univ, true_and] at hr hr'
      rw [sibL_coins Hb hm st E c _ hf] at hr hr'
      exact thetaMain_injective _ (gateInputsOff_off_unique _ _ _ hr hr')
    calc (candC Hb st E c S).card ≤ (Z ∪ S.biUnion K).card := card_le_card hsub
      _ ≤ Z.card + (S.biUnion K).card := card_union_le _ _
      _ ≤ 1 + ∑ k ∈ S, (K k).card := add_le_add hZ card_biUnion_le
      _ ≤ 1 + ∑ _k ∈ S, 1 := by gcongr with k _; exact hK k
      _ = S.card + 1 := by rw [sum_const, smul_eq_mul, mul_one, add_comm]

/-! ## A sibling gate input of a simulated proof against fixed strings -/

/-- **A uniform `d` makes a fixed string a sibling gate input with probability `≤ 2⁻¹²⁸`**: for a
list `tg` of at most `N` byte strings, a statement, a cipher, the simulator's other coins and a
witness prefix `r`, none depending on the field `d`,

    Pr_d[ some string of tg is in sibL r ] ≤ (N + 1)·2⁻¹²⁸. -/
theorem pr_sib_hit_le (hm : MainP p) (st : Statement) (E : Cipher) (sh : Shared)
    (c₁ : Bytes (16 * p.correctionBytes)) (c₂ : Bytes (p.nMask * p.nMultBytes)) (c₃ : Bytes 64)
    (c₅ : Bytes (16 * (p.qsDegree - 1))) (r : Bytes 16) (tg : List ByteArray) {N : ℕ}
    (hN : tg.length ≤ N) :
    pr (Bytes p.witnessBytes) (fun d => ∃ x ∈ tg, x ∈ sibL Hb p st E (sh, (c₁, c₂, c₃, d, c₅)) r) ≤
      (N + 1) / 2 ^ 128 := by
  classical
  rcases hf : firstHit sh.2.1 with _ | ⟨ctr, δ⟩
  · refine le_trans (le_of_eq ?_) (by positivity : (0 : ℝ) ≤ (N + 1) / 2 ^ 128)
    rw [pr_congr (Q := fun _ => False) fun d => by
      rw [sibL_of_none Hb st E (sh, (c₁, c₂, c₃, d, c₅)) r hf]; simp]
    exact pr_false
  · -- the offsets at which some string of `tg` is a gate input
    let iv := (@pubOf (icPrg E) Hb (withP st p) sh δ).iv
    let q := @qcolsOf (icPrg E) (withP st p) (@pubOf (icPrg E) Hb (withP st p) sh δ) δ (ba c₁)
    let Gx : ByteArray → Finset W128 := fun x =>
      if h : ∃ θ, x ∈ Prover.gateInputsOff p CrtGen.tables iv q θ then {h.choose} else ∅
    let G : Finset W128 := tg.toFinset.biUnion Gx
    have hGx : ∀ x θ, x ∈ Prover.gateInputsOff p CrtGen.tables iv q θ → θ ∈ Gx x := by
      intro x θ hθ
      have hex : ∃ θ, x ∈ Prover.gateInputsOff p CrtGen.tables iv q θ := ⟨θ, hθ⟩
      simp only [Gx, hex, ↓reduceDIte, mem_singleton]
      exact gateInputsOff_off_unique _ _ _ hθ hex.choose_spec
    have hG : G.card ≤ N + 1 := by
      have hx : ∀ x, (Gx x).card ≤ 1 := fun x => by
        simp only [Gx]
        split <;> simp
      calc G.card ≤ ∑ x ∈ tg.toFinset, (Gx x).card := card_biUnion_le
        _ ≤ ∑ _x ∈ tg.toFinset, 1 := by gcongr with x _; exact hx x
        _ = tg.toFinset.card := by rw [sum_const, smul_eq_mul, mul_one]
        _ ≤ N + 1 := (List.toFinset_card_le _).trans (hN.trans (Nat.le_succ _))
    have key := pr_thetaMain_le (n := p.witnessBytes) hm.hw (Ω := Unit) (fun _ => r) (fun _ => G)
      (q := N) (fun _ => hG)
    rw [pr_prod_fst (β := Unit)
      (fun d : Bytes p.witnessBytes => thetaMain (pre16 hm.hw d) r ∈ G)] at key
    refine le_trans (pr_mono fun d hd => ?_) key
    obtain ⟨x, hx, hxs⟩ := hd
    rw [sibL_coins Hb hm st E (sh, (c₁, c₂, c₃, d, c₅)) r hf] at hxs
    simp only [G, mem_biUnion, List.mem_toFinset]
    exact ⟨x, hx, hGx x _ hxs⟩

end Sim


/-! ## Optional statements: the slots of a game with all proofs simulated -/

section Opt

variable (Hb : Hashes) (p : Params)

/-- The statement and the witness prefix of an optional statement. -/
def qOf (y : Option SW) : Option (Statement × Bytes 16) := y.map fun y => (y.1, wPre y.2)

/-- The sibling gate inputs of a slot's simulated proof (none without a statement). -/
noncomputable def sibO (q : Option (Statement × Bytes 16)) (E : Cipher) (c : SimCoins p) :
    List ByteArray :=
  match q with
  | some x => sibL Hb p x.1 E c x.2
  | none => []

/-- The active gate inputs of a slot's simulated proof. -/
noncomputable def actO (q : Option (Statement × Bytes 16)) (E : Cipher) (c : SimCoins p) :
    List ByteArray :=
  match q with
  | some x => actL Hb p x.1 E c
  | none => []

/-- The slot's label offset is zero. -/
def zeroO (q : Option (Statement × Bytes 16)) (c : SimCoins p) : Prop :=
  match q with
  | some x => zeroC p c x.2
  | none => False

variable {p}

/-- **The slot's witness prefix is a candidate** of the key set `S` on its simulated proof. -/
def candO (q : Option (Statement × Bytes 16)) (E : Cipher) (c : SimCoins p)
    (S : Finset (Bytes 37)) : Prop :=
  match q with
  | some x => x.2 ∈ candC Hb x.1 E c S
  | none => False

lemma slotErr_simO (y : Option SW) (c : SimCoins p) :
    slotErr (y.map fun _ => simulate p c) → errC p c := by
  rcases y with _ | y
  · rintro ⟨e, he⟩; cases he
  · exact (slotErr_sim c).1

lemma slotZero_simO (y : Option SW) (c : SimCoins p) :
    slotZero p y (y.map fun _ => simulate p c) ↔ zeroO p (qOf y) c := by
  rcases y with _ | y
  · exact Iff.rfl
  · exact slotZero_sim y c

lemma slotHit_simO (y : Option SW) (c : SimCoins p) (E : Cipher) (k : Bytes 37) :
    slotHit Hb p y (y.map fun _ => simulate p c) E k ↔ enc5 k ∈ sibO Hb p (qOf y) E c := by
  rcases y with _ | y
  · show False ↔ enc5 k ∈ ([] : List ByteArray)
    simp
  · exact slotHit_sim Hb y c E k

lemma slotKeys_simO (y : Option SW) (c : SimCoins p) (E : Cipher) :
    slotKeys Hb p y (y.map fun _ => simulate p c) E =
      (actO Hb p (qOf y) E c).toFinset.image (blk 37) ∪
        (sibO Hb p (qOf y) E c).toFinset.image (blk 37) := by
  rcases y with _ | y
  · show (∅ : Finset (Bytes 37)) = ([] : List ByteArray).toFinset.image (blk 37) ∪
      ([] : List ByteArray).toFinset.image (blk 37)
    simp
  · exact slotKeys_sim Hb y c E

lemma sibO_size (hHb : HashesWF Hb) (q : Option (Statement × Bytes 16)) (E : Cipher)
    (c : SimCoins p) {x : ByteArray} (hx : x ∈ sibO Hb p q E c) : x.size = 37 := by
  rcases q with _ | q
  · simp [sibO] at hx
  · exact sibL_size Hb hHb _ _ _ _ hx

lemma sibO_length_le (q : Option (Statement × Bytes 16)) (E : Cipher) (c : SimCoins p) :
    (sibO Hb p q E c).length ≤ 312 := by
  rcases q with _ | q
  · simp [sibO]
  · exact sibL_length_le Hb _ _ _ _

set_option maxRecDepth 8000 in
lemma candO_of_zero {q : Option (Statement × Bytes 16)} {E : Cipher} {c : SimCoins p}
    {S : Finset (Bytes 37)} (h : zeroO p q c) : candO Hb q E c S := by
  rcases q with _ | q
  · exact h
  · show q.2 ∈ candC Hb q.1 E c S
    exact (mem_candC Hb (st := q.1) (E := E) (c := c) (S := S) (r := q.2)).2 (Or.inl h)

set_option maxRecDepth 8000 in
lemma candO_of_key {q : Option (Statement × Bytes 16)} {E : Cipher} {c : SimCoins p}
    {S : Finset (Bytes 37)} (h : ∃ k ∈ S, enc5 k ∈ sibO Hb p q E c) : candO Hb q E c S := by
  rcases q with _ | q
  · obtain ⟨k, -, hk⟩ := h
    simp [sibO] at hk
  · show q.2 ∈ candC Hb q.1 E c S
    exact (mem_candC Hb (st := q.1) (E := E) (c := c) (S := S) (r := q.2)).2 (Or.inr h)

/-- A key of the event's read set or of three other proofs that is in a list `L`: a key of the
public set `S` (the read set and the active inputs), or a sibling input of one of the three. -/
lemma key_split {S R Ka Kb Kc : Finset (Bytes 37)} {la lb lc sa sb sc L : List ByteArray}
    (hR : R ⊆ S) (hla : la.toFinset.image (blk 37) ⊆ S) (hlb : lb.toFinset.image (blk 37) ⊆ S)
    (hlc : lc.toFinset.image (blk 37) ⊆ S)
    (hKa : Ka = la.toFinset.image (blk 37) ∪ sa.toFinset.image (blk 37))
    (hKb : Kb = lb.toFinset.image (blk 37) ∪ sb.toFinset.image (blk 37))
    (hKc : Kc = lc.toFinset.image (blk 37) ∪ sc.toFinset.image (blk 37))
    (hsa : ∀ x ∈ sa, x.size = 37) (hsb : ∀ x ∈ sb, x.size = 37) (hsc : ∀ x ∈ sc, x.size = 37)
    (h : ∃ k ∈ R ∪ (Ka ∪ Kb ∪ Kc), enc5 k ∈ L) :
    (∃ k ∈ S, enc5 k ∈ L) ∨ (∃ x ∈ sa, x ∈ L) ∨ (∃ x ∈ sb, x ∈ L) ∨ (∃ x ∈ sc, x ∈ L) := by
  classical
  obtain ⟨k, hk, hL⟩ := h
  have hsib : ∀ {s : List ByteArray}, (∀ x ∈ s, x.size = 37) → k ∈ s.toFinset.image (blk 37) →
      ∃ x ∈ s, x ∈ L := by
    intro s hs hks
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hks
    rw [List.mem_toFinset] at hx
    refine ⟨x, hx, ?_⟩
    have : enc5 (blk 37 x) = x := ba_blk_of_size (hs x hx)
    rwa [this] at hL
  subst hKa hKb hKc
  simp only [mem_union] at hk
  rcases hk with hk | ((hk | hk) | hk | hk) | hk | hk
  · exact Or.inl ⟨k, hR hk, hL⟩
  · exact Or.inl ⟨k, hla hk, hL⟩
  · exact Or.inr (Or.inl (hsib hsa hk))
  · exact Or.inl ⟨k, hlb hk, hL⟩
  · exact Or.inr (Or.inr (Or.inl (hsib hsb hk)))
  · exact Or.inl ⟨k, hlc hk, hL⟩
  · exact Or.inr (Or.inr (Or.inr (hsib hsc hk)))

end Opt

/-! ## `bstar` with all four proofs simulated -/

section Bstar

variable {S : Type} {p₁ p₂ p₃ p₄ : Params} (Hb : Hashes) (G : Game S Out SW SW SW SW)

/-- **`bstar` on simulated proofs**: a simulation failed, or some slot's witness prefix is a
candidate of the public key set `R ∪ (the four proofs' active gate inputs)`, or a sibling gate
input of an earlier proof is a sibling gate input of a later one. -/
theorem bstar_sim (hHb : HashesWF Hb) (s : S) (E : Cipher) (c₁ : SimCoins p₁) (c₂ : SimCoins p₂)
    (c₃ : SimCoins p₃) (c₄ : SimCoins p₄) (R : Finset (Bytes 37))
    (o₁ o₂ o₃ o₄ : Option Out) (q₁ q₂ q₃ q₄ : Option (Statement × Bytes 16))
    (ho₁ : o₁ = (G.σ₁ s).map fun _ => simulate p₁ c₁)
    (ho₂ : o₂ = (G.σ₂ s o₁).map fun _ => simulate p₂ c₂)
    (ho₃ : o₃ = (G.σ₃ s o₁ o₂).map fun _ => simulate p₃ c₃)
    (ho₄ : o₄ = (G.σ₄ s o₁ o₂ o₃).map fun _ => simulate p₄ c₄)
    (hq₁ : q₁ = qOf (G.σ₁ s)) (hq₂ : q₂ = qOf (G.σ₂ s o₁)) (hq₃ : q₃ = qOf (G.σ₃ s o₁ o₂))
    (hq₄ : q₄ = qOf (G.σ₄ s o₁ o₂ o₃)) (Sp : Finset (Bytes 37))
    (hSp : Sp = R ∪ ((actO Hb p₁ q₁ E c₁).toFinset.image (blk 37) ∪
      (actO Hb p₂ q₂ E c₂).toFinset.image (blk 37) ∪ (actO Hb p₃ q₃ E c₃).toFinset.image (blk 37) ∪
      (actO Hb p₄ q₄ E c₄).toFinset.image (blk 37)))
    (h : bstarCore (p₁ := p₁) (p₂ := p₂) (p₃ := p₃) (p₄ := p₄) Hb G s o₁ o₂ o₃ o₄ E R) :
    (errC p₁ c₁ ∨ errC p₂ c₂ ∨ errC p₃ c₃ ∨ errC p₄ c₄) ∨
    (candO Hb q₁ E c₁ Sp ∨ candO Hb q₂ E c₂ Sp ∨ candO Hb q₃ E c₃ Sp ∨ candO Hb q₄ E c₄ Sp) ∨
    ((∃ x ∈ sibO Hb p₁ q₁ E c₁, x ∈ sibO Hb p₂ q₂ E c₂) ∨
      (∃ x ∈ sibO Hb p₁ q₁ E c₁ ++ sibO Hb p₂ q₂ E c₂, x ∈ sibO Hb p₃ q₃ E c₃) ∨
      (∃ x ∈ sibO Hb p₁ q₁ E c₁ ++ sibO Hb p₂ q₂ E c₂ ++ sibO Hb p₃ q₃ E c₃,
        x ∈ sibO Hb p₄ q₄ E c₄)) := by
  classical
  have hR : R ⊆ Sp := by rw [hSp]; exact subset_union_left
  have ha₁ : (actO Hb p₁ q₁ E c₁).toFinset.image (blk 37) ⊆ Sp := by
    rw [hSp]; intro k hk; simp only [mem_union]; tauto
  have ha₂ : (actO Hb p₂ q₂ E c₂).toFinset.image (blk 37) ⊆ Sp := by
    rw [hSp]; intro k hk; simp only [mem_union]; tauto
  have ha₃ : (actO Hb p₃ q₃ E c₃).toFinset.image (blk 37) ⊆ Sp := by
    rw [hSp]; intro k hk; simp only [mem_union]; tauto
  have ha₄ : (actO Hb p₄ q₄ E c₄).toFinset.image (blk 37) ⊆ Sp := by
    rw [hSp]; intro k hk; simp only [mem_union]; tauto
  have hs₁ := fun x hx => sibO_size Hb hHb q₁ E c₁ (x := x) hx
  have hs₂ := fun x hx => sibO_size Hb hHb q₂ E c₂ (x := x) hx
  have hs₃ := fun x hx => sibO_size Hb hHb q₃ E c₃ (x := x) hx
  have hs₄ := fun x hx => sibO_size Hb hHb q₄ E c₄ (x := x) hx
  have hK₁ := slotKeys_simO Hb (G.σ₁ s) c₁ E
  have hK₂ := slotKeys_simO Hb (G.σ₂ s o₁) c₂ E
  have hK₃ := slotKeys_simO Hb (G.σ₃ s o₁ o₂) c₃ E
  have hK₄ := slotKeys_simO Hb (G.σ₄ s o₁ o₂ o₃) c₄ E
  rw [← ho₁, ← hq₁] at hK₁
  rw [← ho₂, ← hq₂] at hK₂
  rw [← ho₃, ← hq₃] at hK₃
  rw [← ho₄, ← hq₄] at hK₄
  have hH₁ : ∀ k, slotHit Hb p₁ (G.σ₁ s) o₁ E k ↔ enc5 k ∈ sibO Hb p₁ q₁ E c₁ := fun k => by
    rw [ho₁, hq₁]; exact slotHit_simO Hb _ c₁ E k
  have hH₂ : ∀ k, slotHit Hb p₂ (G.σ₂ s o₁) o₂ E k ↔ enc5 k ∈ sibO Hb p₂ q₂ E c₂ := fun k => by
    rw [ho₂, hq₂]; exact slotHit_simO Hb _ c₂ E k
  have hH₃ : ∀ k, slotHit Hb p₃ (G.σ₃ s o₁ o₂) o₃ E k ↔ enc5 k ∈ sibO Hb p₃ q₃ E c₃ := fun k => by
    rw [ho₃, hq₃]; exact slotHit_simO Hb _ c₃ E k
  have hH₄ : ∀ k, slotHit Hb p₄ (G.σ₄ s o₁ o₂ o₃) o₄ E k ↔ enc5 k ∈ sibO Hb p₄ q₄ E c₄ :=
    fun k => by rw [ho₄, hq₄]; exact slotHit_simO Hb _ c₄ E k
  have hZ₁ : slotZero p₁ (G.σ₁ s) o₁ → zeroO p₁ q₁ c₁ := by
    rw [ho₁, hq₁]; exact (slotZero_simO _ c₁).1
  have hZ₂ : slotZero p₂ (G.σ₂ s o₁) o₂ → zeroO p₂ q₂ c₂ := by
    rw [ho₂, hq₂]; exact (slotZero_simO _ c₂).1
  have hZ₃ : slotZero p₃ (G.σ₃ s o₁ o₂) o₃ → zeroO p₃ q₃ c₃ := by
    rw [ho₃, hq₃]; exact (slotZero_simO _ c₃).1
  have hZ₄ : slotZero p₄ (G.σ₄ s o₁ o₂ o₃) o₄ → zeroO p₄ q₄ c₄ := by
    rw [ho₄, hq₄]; exact (slotZero_simO _ c₄).1
  rcases h with he | h1 | h2 | h3 | h4
  · left
    rcases he with he | he | he | he
    · exact Or.inl (slotErr_simO _ c₁ (ho₁ ▸ he))
    · exact Or.inr (Or.inl (slotErr_simO _ c₂ (ho₂ ▸ he)))
    · exact Or.inr (Or.inr (Or.inl (slotErr_simO _ c₃ (ho₃ ▸ he))))
    · exact Or.inr (Or.inr (Or.inr (slotErr_simO _ c₄ (ho₄ ▸ he))))
  · right
    rcases h1 with hz | ⟨k, hk, hx⟩
    · exact Or.inl (Or.inl (candO_of_zero Hb (hZ₁ hz)))
    · rcases key_split hR ha₂ ha₃ ha₄ hK₂ hK₃ hK₄ hs₂ hs₃ hs₄ ⟨k, hk, (hH₁ k).1 hx⟩ with
        h | ⟨x, hx, hx'⟩ | ⟨x, hx, hx'⟩ | ⟨x, hx, hx'⟩
      · exact Or.inl (Or.inl (candO_of_key Hb h))
      · exact Or.inr (Or.inl ⟨x, hx', hx⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨x, List.mem_append_left _ hx', hx⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨x, List.mem_append_left _ (List.mem_append_left _ hx'), hx⟩))
  · right
    rcases h2 with hz | ⟨k, hk, hx⟩
    · exact Or.inl (Or.inr (Or.inl (candO_of_zero Hb (hZ₂ hz))))
    · rcases key_split hR ha₁ ha₃ ha₄ hK₁ hK₃ hK₄ hs₁ hs₃ hs₄ ⟨k, hk, (hH₂ k).1 hx⟩ with
        h | ⟨x, hx, hx'⟩ | ⟨x, hx, hx'⟩ | ⟨x, hx, hx'⟩
      · exact Or.inl (Or.inr (Or.inl (candO_of_key Hb h)))
      · exact Or.inr (Or.inl ⟨x, hx, hx'⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨x, List.mem_append_right _ hx', hx⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨x, List.mem_append_left _ (List.mem_append_right _ hx'), hx⟩))
  · right
    rcases h3 with hz | ⟨k, hk, hx⟩
    · exact Or.inl (Or.inr (Or.inr (Or.inl (candO_of_zero Hb (hZ₃ hz)))))
    · rcases key_split hR ha₁ ha₂ ha₄ hK₁ hK₂ hK₄ hs₁ hs₂ hs₄ ⟨k, hk, (hH₃ k).1 hx⟩ with
        h | ⟨x, hx, hx'⟩ | ⟨x, hx, hx'⟩ | ⟨x, hx, hx'⟩
      · exact Or.inl (Or.inr (Or.inr (Or.inl (candO_of_key Hb h))))
      · exact Or.inr (Or.inr (Or.inl ⟨x, List.mem_append_left _ hx, hx'⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨x, List.mem_append_right _ hx, hx'⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨x, List.mem_append_right _ hx', hx⟩))
  · right
    rcases h4 with hz | ⟨k, hk, hx⟩
    · exact Or.inl (Or.inr (Or.inr (Or.inr (candO_of_zero Hb (hZ₄ hz)))))
    · rcases key_split hR ha₁ ha₂ ha₃ hK₁ hK₂ hK₃ hs₁ hs₂ hs₃ ⟨k, hk, (hH₄ k).1 hx⟩ with
        h | ⟨x, hx, hx'⟩ | ⟨x, hx, hx'⟩ | ⟨x, hx, hx'⟩
      · exact Or.inl (Or.inr (Or.inr (Or.inr (candO_of_key Hb h))))
      · exact Or.inr (Or.inr (Or.inr ⟨x, List.mem_append_left _ (List.mem_append_left _ hx), hx'⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨x, List.mem_append_left _ (List.mem_append_right _ hx), hx'⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨x, List.mem_append_right _ hx, hx'⟩))

end Bstar

/-! ## Probabilities on a slot's coins -/

section Peel

variable {p : Params}

/-- A bound for every value of the other coins of a slot is a bound over the slot's coins, with
the simulator's field `d` separated. -/
theorem pr_KS_d_le (P : KS p → Prop) {ε : ℝ}
    (h : ∀ (ρ : Bytes 16) (sh : Shared) (c₁ : Bytes (16 * p.correctionBytes))
      (c₂ : Bytes (p.nMask * p.nMultBytes)) (c₃ : Bytes 64) (c₅ : Bytes (16 * (p.qsDegree - 1)))
      (V : VP p), pr (Bytes p.witnessBytes) (fun d => P ((ρ, (sh, (c₁, c₂, c₃, d, c₅))), V)) ≤ ε) :
    pr (KS p) P ≤ ε := by
  refine pr_le_of_snd fun V => pr_le_of_fst fun ρ => pr_le_of_fst fun sh => pr_le_of_fst fun c₁ =>
    pr_le_of_fst fun c₂ => pr_le_of_fst fun c₃ => pr_le_of_snd fun c₅ => ?_
  exact h ρ sh c₁ c₂ c₃ c₅ V

/-- **A simulation fails with probability `noHitProb`** (no accepted grinding answer). -/
theorem pr_errC_le : pr (KS p) (fun k => errC p k.1.2) ≤ noHitProb := by
  refine pr_le_of_snd fun V => pr_le_of_fst fun ρ => pr_le_of_snd fun f => pr_le_of_fst fun iv =>
    pr_le_of_snd fun r => ?_
  refine le_of_eq (pr_congr fun g => ?_)
  show errC p (((ρ, ((iv, g, r), f)), V) : KS p).1.2 ↔ firstHit g = none
  unfold errC simulate
  rcases hf : firstHit g with _ | ⟨ctr, δ⟩
  · simp
  · simp

end Peel

end VoleMole.ZK.Sim
