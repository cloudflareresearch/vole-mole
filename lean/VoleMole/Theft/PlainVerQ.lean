import VoleMole.Theft.PlainEager
import VoleMole.ROM.ChainParse

/-!
# The verifier queries only table points

For `pr_tables_eq_ro` (`Theft/PlainEager.lean`) every query of `ROM/`'s game must be a table
point: the prover's (normalized, `normT`), the straight-line extractor's (`mu₁`, `iv`) and the
verifier's. Here the verifier (`verifyQ`, query by query) is shown to query only table points
(`docs/security/ratatouille.md` §5, item 4 (b)), for a non-delayed statement whose inputs fit
(`VerOk`):

* `mu₁`: `muIn st`, of at most `L` bytes;
* `H₄`: `iv_pre ‖ mu₁ ‖ 4`, `49` bytes;
* `H₁`: the 17 leaf inputs (at most `2⁸·32 + 1 = 8193` bytes) and the commitment input
  (`17·32 + 1` bytes);
* `H₂¹`, `H₂²`: the chain inputs (the sizes of `Theft/HitLevel.lean`'s `FOk`);
* `H₅`: the gate inputs, `iv ‖ e ‖ row ‖ 5`, exactly 37 bytes;
* the combination: `chal2 ‖ dst`, of the table's `M`;
* `H₂³`: `chal2 ‖ check ‖ ã ‖ ctr ‖ 11`, a grinding point (`enc2 p`) when the proof has its format:
  the prefix has `preLen` bytes and the 4-byte counter is a little-endian `UInt32`
  (`pushLE32_getLE32`).

`verifyQ_onT` is the statement; `verOk_stI`, `verOk_stS` check it for the Lean Ratatouille
statements with `L ≥ Hit.Rata.Lmin` and `M = uovM`.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open OracleComp OracleSpec

namespace VoleMole.Theft

open VoleMole.Privacy VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge
open VoleMole.ROM VoleMole.ROM.IC VoleMole.ROM.Reads

/-! ## Four bytes as a little-endian counter -/

lemma toUInt8_le32 (b0 b1 b2 b3 : UInt8) :
    let x := b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)
    x.toUInt8 = b0 ∧ (x >>> 8).toUInt8 = b1 ∧ (x >>> 16).toUInt8 = b2 ∧
      (x >>> 24).toUInt8 = b3 := by
  intro x
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [x] <;> bv_decide

/-- **A 4-byte suffix is the little-endian encoding of its counter.** -/
lemma pushLE32_getLE32 (pre b : ByteArray) (hb : b.size = 4) :
    AES.pushLE32 pre (AES.getLE32 b 0) = pre ++ b := by
  obtain ⟨⟨l⟩⟩ := b
  match l, hb with
  | [a0, a1, a2, a3], _ =>
    obtain ⟨h0, h1, h2, h3⟩ := toUInt8_le32 a0 a1 a2 a3
    have e : AES.getLE32 ⟨#[a0, a1, a2, a3]⟩ 0 = a0.toUInt32 ||| (a1.toUInt32 <<< 8) |||
        (a2.toUInt32 <<< 16) ||| (a3.toUInt32 <<< 24) := rfl
    rw [e]
    unfold AES.pushLE32
    rw [h0, h1, h2, h3]
    apply ByteArray.ext
    simp only [ByteArray.data_append, ByteArray.push]
    apply Array.ext'
    simp

/-! ## Table points of each kind -/

section Pts

variable {p : Params} {L M : ℕ}

lemma mem_TPts_encL {k : Kind}
    (hk : k = .h1 ∨ k = .mu ∨ k = .muDelayed ∨ k = .h4 ∨ k = .h21 ∨ k = .h22 ∨ k = .comb M)
    {b : ByteArray} (hb : b.size ≤ L) : (k, b) ∈ TPts p L M := by
  obtain ⟨a, rfl⟩ := Hit.exists_encL (L := L) hb
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tpt_mem p L M (.inr (.inr (.inr (.inl a))))
  · exact tpt_mem p L M (.inr (.inr (.inr (.inr (.inl a)))))
  · exact tpt_mem p L M (.inr (.inr (.inr (.inr (.inr (.inl a))))))
  · exact tpt_mem p L M (.inr (.inr (.inr (.inr (.inr (.inr (.inl a)))))))
  · exact tpt_mem p L M (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl a))))))))
  · exact tpt_mem p L M (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl a)))))))))
  · exact tpt_mem p L M (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr a)))))))))

lemma mem_TPts_h5 {b : ByteArray} (hb : b.size = 37) : ((.h5, b) : Dom) ∈ TPts p L M := by
  have h := tpt_mem p L M (.inr (.inr (.inl (blk 37 b))))
  have e : enc5 (blk 37 b) = b := ba_blk_of_size hb
  simpa only [tpt, e] using h

/-- **The `H₂³` input of a formatted proof is a grinding point.** -/
lemma mem_TPts_h23 {pre ctr : ByteArray} (hpre : pre.size = preLen p) (hc : ctr.size = 4) :
    ((.h23, (pre ++ ctr).push 11) : Dom) ∈ TPts p L M := by
  let c : Fin nGrind := ⟨(AES.getLE32 ctr 0).toNat, by
    simp only [nGrind]; exact (AES.getLE32 ctr 0).toNat_lt⟩
  have h := tpt_mem p L M (.inr (.inl (blk (preLen p) pre, c)))
  have hc' : c.val.toUInt32 = AES.getLE32 ctr 0 :=
    UInt32.toNat_inj.1 (toNat_toUInt32 (AES.getLE32 ctr 0).toNat_lt)
  have e : enc2 p (blk (preLen p) pre, c) = (pre ++ ctr).push 11 := by
    show (AES.pushLE32 (ba (blk (preLen p) pre)) c.val.toUInt32).push 11 = _
    rw [ba_blk_of_size hpre, hc', pushLE32_getLE32 _ _ hc]
  simpa only [tpt, e] using h

end Pts

/-! ## Queries of a computation, by steps -/

section AllQ

variable {α : Type} {P : Dom → Prop}

lemma allQ_hashQ_bind_iff {k : Kind} {x : ByteArray} {f : ByteArray → OracleComp spec α} :
    AllQueriesSatisfy (hashQ k x >>= f) P ↔
      P (k, x) ∧ ∀ u : Ans (k, x), AllQueriesSatisfy (f u.ba) P := by
  rw [hashQ_bind]; exact allQueriesSatisfy_query_bind_iff _ _ _

/-- `l.length` queries to `k`, then `f` on answers of `k.outLen` bytes. -/
lemma allQ_mapM_hashQ_bind (k : Kind) (l : List ByteArray) {f : List ByteArray → OracleComp spec α}
    (hl : ∀ x ∈ l, P (k, x))
    (hf : ∀ ans : List ByteArray, ans.length = l.length → (∀ y ∈ ans, y.size = k.outLen) →
      AllQueriesSatisfy (f ans) P) :
    AllQueriesSatisfy (l.mapM (hashQ k) >>= f) P := by
  induction l generalizing f with
  | nil => simpa using hf [] rfl (by simp)
  | cons x l ih =>
    simp only [List.mapM_cons, bind_assoc, pure_bind]
    refine allQ_hashQ_bind_iff.2 ⟨hl x (by simp), fun u => ?_⟩
    refine ih (fun y hy => hl y (by simp [hy])) fun ans hlen hsz => ?_
    refine hf (u.ba :: ans) (by simp [hlen]) fun y hy => ?_
    rcases List.mem_cons.1 hy with rfl | hy
    · exact Prob.Bytes.size_ba u
    · exact hsz y hy

lemma size_foldl_append (l : List ByteArray) (acc : ByteArray) :
    (l.foldl (· ++ ·) acc).size = acc.size + (l.map ByteArray.size).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons x l ih => simp [ih, ByteArray.size_append]; omega

end AllQ

/-! ## The verifier -/

section Ver

variable {p : Params} {L M : ℕ}

/-- **The verifier's inputs fit the tables**: a non-delayed statement with the prefix length of
`p`, `mu₁` and the chain inputs of at most `L` bytes, leaf inputs of at most `L` bytes, and a
combination of the table's `M` with an input of at most `L` bytes. -/
def VerOk (p : Params) (L M : ℕ) (st : Statement) : Prop :=
  st.delayed = false ∧ preLen st.params = preLen p ∧ (muIn st).size ≤ L ∧
    64 + 16 * st.params.correctionBytes + st.params.nMask * st.params.nMultBytes + 16 +
      st.binder1.size + 1 ≤ L ∧
    264 + st.binder2.size + st.params.witnessBytes + 1 ≤ L ∧ 8193 ≤ L ∧
    ∀ M' dst, st.comb = some (M', dst) → M' = M ∧ 56 + dst.size ≤ L

lemma kOf_le (i : ℕ) : BAVC.kOf i ≤ 8 := by unfold BAVC.kOf; split <;> omega

variable [HasPrg]

/-- **The verifier queries only table points**, for a statement whose inputs fit (`VerOk`). -/
theorem verifyQ_onT (T : CrtTables) (st : Statement) (proof : ByteArray) (h : VerOk p L M st) :
    AllQueriesSatisfy (verifyQ T st proof) (· ∈ TPts p L M) := by
  obtain ⟨hd, hpre, hmu, h1, h2, hleaf, hcomb⟩ := h
  unfold verifyQ
  dsimp only
  split
  · exact allQueriesSatisfy_pure _ _
  rename_i hf
  have hfmt : (⟨st.params, proof⟩ : Proof).checkFormat = true := by simpa using hf
  have hm1 : mu1Q st = hashQ .mu (muIn st) := by simp [mu1Q, hd, muIn]
  rw [hm1]
  refine allQ_hashQ_bind_iff.2 ⟨mem_TPts_encL (by simp) hmu, fun mu1 => ?_⟩
  refine allQ_hashQ_bind_iff.2 ⟨mem_TPts_encL (by simp) ?_, fun iv => ?_⟩
  · have := Chain.size_field_le (⟨st.params, proof⟩ : Proof) (Params.field_ivPre st.params)
    have hm : (Prob.Bytes.ba mu1).size = 32 := Prob.Bytes.size_ba mu1
    simp only [ByteArray.size_push, ByteArray.size_append, hm, Proof.ivPre] at this ⊢
    omega
  split
  · exact allQueriesSatisfy_pure _ _
  rename_i leaves _
  refine allQ_mapM_hashQ_bind _ _ (fun x hx => mem_TPts_encL (by simp) ?_) fun lh hlen hsz => ?_
  · simp only [BAVC.leafHashInputs, List.mem_map, List.mem_range] at hx
    obtain ⟨i, -, rfl⟩ := hx
    have h8 : 2 ^ BAVC.kOf i ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (kOf_le i)
    simp only [ByteArray.size_push, ByteArray.size_extract, BAVC.hashLen]
    omega
  refine allQ_hashQ_bind_iff.2 ⟨mem_TPts_encL (by simp) ?_, fun com => ?_⟩
  · have e : lh.map ByteArray.size = lh.map fun _ => 32 :=
      List.map_congr_left fun y hy => hsz y hy
    rw [length_leafHashInputs] at hlen
    simp only [BAVC.comInput, ByteArray.size_push, size_foldl_append, e, List.map_const',
      List.sum_replicate, hlen, ByteArray.size_empty, smul_eq_mul]
    omega
  refine allQ_hashQ_bind_iff.2 ⟨mem_TPts_encL (by simp) ?_, fun c1 => ?_⟩
  · have e1 := Chain.size_field_le (⟨st.params, proof⟩ : Proof) (Params.field_corrections st.params)
    have e2 := Chain.size_field_le (⟨st.params, proof⟩ : Proof) (Params.field_cmult st.params)
    have e3 := Chain.size_field_le (⟨st.params, proof⟩ : Proof) (Params.field_ivPre st.params)
    have hm : (Prob.Bytes.ba mu1).size = 32 := Prob.Bytes.size_ba mu1
    have hc' : (Prob.Bytes.ba com).size = 32 := Prob.Bytes.size_ba com
    simp only [chal1Input, ByteArray.size_push, ByteArray.size_append, hm, hc',
      Proof.corrections, Proof.cmult, Proof.ivPre] at e1 e2 e3 ⊢
    omega
  refine allQ_mapM_hashQ_bind _ _ (fun x hx => mem_TPts_h5 ?_) fun gh _ _ => ?_
  · simp only [gateInputs, List.mem_map, List.mem_range] at hx
    obtain ⟨e, -, rfl⟩ := hx
    have hiv : (Prob.Bytes.ba iv).size = 16 := Prob.Bytes.size_ba iv
    simp only [ByteArray.size_push, ByteArray.size_append, size_pushLE32, W128.toBytes_size, hiv]
  rw [show muDelayedQ st c1.ba = pure ByteArray.empty by simp [muDelayedQ, hd], pure_bind]
  refine allQ_hashQ_bind_iff.2 ⟨mem_TPts_encL (by simp) ?_, fun c2 => ?_⟩
  · have e1 := Chain.size_field_le (⟨st.params, proof⟩ : Proof) (Params.field_voleCheck st.params)
    have e2 := Chain.size_field_le (⟨st.params, proof⟩ : Proof) (Params.field_correction st.params)
    have hc' : (Prob.Bytes.ba c1).size = 136 := Prob.Bytes.size_ba c1
    simp only [chal2Input, ByteArray.size_push, ByteArray.size_append, hc', Chain.size_hb _ (voleHashReceiver_size _ _ _ _ _ _), ByteArray.size_empty,
      Proof.voleCheck, Proof.correction] at e1 e2 ⊢
    omega
  split
  · exact allQueriesSatisfy_pure _ _
  have hq : (((⟨st.params, proof⟩ : Proof).qsProof).size = (st.params.qsDegree - 1) * 16) :=
    size_field _ hfmt (Params.field_qsProof st.params) (by
      rw [Params.proofBytes_eq]; simp only [Params.o₇, Params.o₅]; omega)
  have hc : ((⟨st.params, proof⟩ : Proof).ctr).size = 4 :=
    size_field _ hfmt (Params.field_ctr st.params) (by rw [Params.proofBytes_eq])
  have h23 : ∀ check (f : ByteArray → OracleComp spec Transcript),
      (∀ x, AllQueriesSatisfy (f x) (· ∈ TPts p L M)) →
      AllQueriesSatisfy (hashQ .h23 (chal3Input ⟨st.params, proof⟩ (Prob.Bytes.ba c2) check) >>= f)
        (· ∈ TPts p L M) := by
    intro check f hf
    refine allQ_hashQ_bind_iff.2 ⟨mem_TPts_h23 ?_ hc, fun c3 => ?_⟩
    · have h56 : (Prob.Bytes.ba c2).size = 56 := Prob.Bytes.size_ba c2
      simp only [ByteArray.size_append, h56, size_gfToBytes, hq]
      rw [← hpre]
      simp only [preLen]
      omega
    · exact hf _
  unfold combBytesQ
  split
  · rw [pure_bind]
    exact h23 _ _ fun _ => allQueriesSatisfy_pure _ _
  · rename_i M' dst heq
    obtain ⟨rfl, hsz'⟩ := hcomb M' dst heq
    refine allQ_hashQ_bind_iff.2 ⟨mem_TPts_encL (by simp) ?_, fun lb =>
      h23 _ _ fun _ => allQueriesSatisfy_pure _ _⟩
    have h56 : (Prob.Bytes.ba c2).size = 56 := Prob.Bytes.size_ba c2
    simp only [ByteArray.size_append, h56]
    omega

end Ver

/-! ## The game -/

section Game

variable {p : Params} {L M : ℕ} {α ι β : Type}

/-- **The hash queries of `runE E P` are `P`'s.** -/
theorem runE_onT (E : CTable) {P : OracleComp specIC α} (hP : AllQueriesSatisfy P (OnT p L M)) :
    AllQueriesSatisfy (runE E P) (· ∈ TPts p L M) := by
  induction P using OracleComp.inductionOn with
  | pure a => exact allQueriesSatisfy_pure _ _
  | query_bind t k ih =>
    obtain ⟨ht, hk⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).1 hP
    cases t with
    | inl d =>
      rw [runE_inl]
      refine (allQueriesSatisfy_query_bind_iff _ _ _).2 ⟨ht, fun u => ?_⟩
      rw [map_eq_bind_pure_comp]
      exact allQueriesSatisfy_bind (ih u (hk u)) fun _ => allQueriesSatisfy_pure _ _
    | inr x =>
      rw [runE_inr, map_eq_bind_pure_comp]
      exact allQueriesSatisfy_bind (ih _ (hk _)) fun _ => allQueriesSatisfy_pure _ _

/-- **The straight-line extractor queries table points** (`mu₁` and `iv`). -/
theorem extractIC_onT (st : Statement) (hst : VerOk p L M st) (E : CTable)
    (r : (ByteArray × β) × QueryLog specIC) :
    AllQueriesSatisfy (extractIC st E r) (· ∈ TPts p L M) := by
  obtain ⟨hd, -, hmu, -, -, hleaf, -⟩ := hst
  unfold extractIC
  have hm1 : mu1Q st = hashQ .mu (muIn st) := by simp [mu1Q, hd, muIn]
  rw [hm1]
  refine allQ_hashQ_bind_iff.2 ⟨mem_TPts_encL (by simp) hmu, fun mu1 => ?_⟩
  refine allQ_hashQ_bind_iff.2 ⟨mem_TPts_encL (by simp) ?_, fun iv => allQueriesSatisfy_pure _ _⟩
  have := Chain.size_field_le (⟨st.params, r.1.1⟩ : Proof) (Params.field_ivPre st.params)
  have hm : (Prob.Bytes.ba mu1).size = 32 := Prob.Bytes.size_ba mu1
  simp only [ByteArray.size_push, ByteArray.size_append, hm, Proof.ivPre] at this ⊢
  omega

/-- **`ROM/`'s adaptive game queries only table points**, for a prover that does and statements
whose inputs fit. -/
theorem gameA_onT (stF : ι → Statement) (hst : ∀ i, VerOk p L M (stF i))
    {P : OracleComp specIC (ByteArray × (ι × β))} (hP : AllQueriesSatisfy P (OnT p L M))
    (E : CTable) : AllQueriesSatisfy (gameA CrtGen.tables stF P E) (· ∈ TPts p L M) := by
  unfold gameA proverA
  refine allQueriesSatisfy_bind (allQueriesSatisfy_bind (runE_onT E hP) fun r =>
    extractIC_onT _ (hst _) E r) fun r => ?_
  rw [map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind (@verifyQ_onT p L M (icPrg E.cipher) _ _ _ (hst _))
    fun _ => allQueriesSatisfy_pure _ _

end Game

/-! ## The Lean Ratatouille statements -/

section Rata

variable {L M : ℕ}

open VoleMole.Privacy.Ratatouille

set_option maxRecDepth 100000 in
open VoleMole.Spec.Ratatouille in
/-- **The Lean issuance statement's inputs fit** the tables with `L ≥ Lmin`. -/
lemma verOk_stI (hL : Hit.Rata.Lmin ≤ L) (x : IssueInstance) :
    VerOk pI L M (Privacy.Ratatouille.stI x) := by
  refine ⟨rfl, by simp [Privacy.Ratatouille.stI, ratatouilleIssue, preLen], ?_, le_trans ?_ hL,
    le_trans ?_ hL, le_trans (by decide) hL, ?_⟩
  · rw [Hit.Rata.size_muIn_stI]; exact le_trans (by decide) hL
  · show 64 + 16 * pI.correctionBytes + pI.nMask * pI.nMultBytes + 16 + 0 + 1 ≤ Hit.Rata.Lmin
    decide
  · show 264 + 0 + pI.witnessBytes + 1 ≤ Hit.Rata.Lmin
    decide
  · intro M' dst h
    exact absurd h (by simp [Privacy.Ratatouille.stI, ratatouilleIssue])

set_option maxRecDepth 100000 in
open VoleMole.Spec.Ratatouille in
/-- **The Lean spend statement's inputs fit** the tables with `L ≥ Lmin` and the combination of
`uovM` equations. -/
lemma verOk_stS (hL : Hit.Rata.Lmin ≤ L) (x : SpendInstance) :
    VerOk pI L Arith.Ratatouille.uovM (Privacy.Ratatouille.stS x) := by
  refine ⟨rfl, by simp [Privacy.Ratatouille.stS, preLen], ?_, le_trans ?_ hL, le_trans ?_ hL, le_trans (by decide) hL, ?_⟩
  · rw [Hit.Rata.size_muIn_stS]; exact le_trans (by decide) hL
  · show 64 + 16 * pS.correctionBytes + pS.nMask * pS.nMultBytes + 16 + 0 + 1 ≤ Hit.Rata.Lmin
    decide
  · show 264 + 0 + pS.witnessBytes + 1 ≤ Hit.Rata.Lmin
    decide
  · intro M' dst h
    simp only [Privacy.Ratatouille.stS, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, le_trans ?_ hL⟩
    decide

end Rata

end VoleMole.Theft
