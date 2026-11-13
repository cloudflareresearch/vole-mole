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

end VoleMole.ZK.Sim
