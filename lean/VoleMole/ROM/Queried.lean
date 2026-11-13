import VoleMole.ROM.Accept

/-!
# The verifier's chain queries were made by the prover (plan M6, "fresh verifier queries")

An accepted proof's chain is the sequence of the verifier's hash queries

    w_i = c_i ‖ 1 (17 leaf hashes, `H₁`) → cw = h_0 ‖ … ‖ h_16 ‖ 1 (`H₁`) → x (`H₂¹`) → y (`H₂²`)
      → z (`H₂³`),

each input containing the previous answer at a fixed position (`h_i = H₁(w_i)` is block `i` of
`cw`, `com = H₁(cw)` is bytes `32 … 64` of `x`, `chal1 = H₂¹(x)` the first 136 bytes of `y`,
`chal2 = H₂²(y)` the first 56 bytes of `z`), and acceptance is `H₂³(z) = Δ`. If one of these
inputs was never queried by the prover, walking up the chain from it the first query that the
prover made contains the answer to a query it did not make (a "hit", `L0-L2` §5 `Hit₁` and its
analogues for `H₂¹`, `H₂²`), or the prover made none and the verifier's `H₂³` answer is the
proof's `Δ`. Both are bad answers of single queries, so VCVio's union bound applies.

* **The interface.** The prover `oa` reports its own queries in its output (`qs aux`, e.g. read off
  its query log), and they behave as a log: updating the table at a cell the prover did not
  query does not change its output (`hfix`, for the kinds of the chain), a queried cell stays
  queried (`hmem`), and it makes at most `q' k` queries of kind `k` (`hcnt`).
* **The bad answers** (`ladderBad`): an answer at a cell the prover did not query, equal to one of
  the targets of `ladderTargets`: a 32-byte block of one of its `H₁` inputs or the `com` field of
  one of its `H₂¹` inputs (`H₁`), the `chal1` field of one of its `H₂²` inputs (`H₂¹`), the `chal2`
  field of one of its `H₂³` inputs (`H₂²`), the proof's `Δ` (`H₂³`).
* **`prEvent_accept_leafUnqueried_le`**: the verifier accepts and one of its 17 leaf-hash inputs
  was not queried by the prover with probability

      ≤ (q₁+18)·(17q'₁+q'₂₁)·2⁻²⁵⁶ + (q₂₁+1)·q'₂₂·2⁻¹⁰⁸⁸ + (q₂₂+1)·q'₂₃·2⁻⁴⁴⁸ + (q₂₃+1)·2⁻¹²⁸,

  `q` the game's prover's per-domain counts (the `+1`, `+18` are the verifier's queries, charged
  by the union bound) and `q'` the prover's own. The last term is the "fresh `H₂³`" step of the
  plan (§2c, M6); the union bound charges it to every `H₂³` query, hence `q₂₃ + 1` rather than
  `1`.
* **`prEvent_accept_leafUnqueried_z_le`**: the same event with the verifier's `H₂³` input
  (`zOut`, read off the transcript; `zOut_eq_runZ`) among the prover's queries: the first three
  terms only (`ladder_walk`). The complementary case, the verifier's own `H₂³` query fresh, is the
  single guess `prEvent_accept_zUnqueried_le` of `ROM/FreshGuess.lean` (`2⁻¹²⁸`).

The generic log facts (`tableQueryLog_update_of_not_mem`, `mem_tableQueryLog_update`) are for any
`OracleSpec.ofFn`.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge

/-! ## Logs against tables updated at a cell -/

section Log

variable {D α : Type} {R : D → Type} [DecidableEq D]

omit [DecidableEq D] in
/-- **Two tables that agree on the cells a computation queries give the same run.** -/
theorem tableQueryLog_congr (oa : OracleComp (ofFn R) α) (f f' : ∀ d, R d)
    (h : ∀ t ∈ (tableQueryLog oa f).map Sigma.fst, f' t = f t) :
    evalWithAnswerFn (QueryImpl.ofFn f') oa = evalWithAnswerFn (QueryImpl.ofFn f) oa ∧
      tableQueryLog oa f' = tableQueryLog oa f := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [tableQueryLog_query_bind, List.map_cons] at h
    have ht : f' t = f t := h t List.mem_cons_self
    obtain ⟨h1, h2⟩ := ih (f t) fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply,
      tableQueryLog_query_bind, ht]
    exact ⟨h1, by rw [h2]⟩

/-- **A queried cell stays queried** under a change of the table at that cell only. -/
theorem mem_tableQueryLog_congr (oa : OracleComp (ofFn R) α) (f f' : ∀ d, R d) (d : D)
    (h : ∀ t, t ≠ d → f' t = f t) (hd : d ∈ (tableQueryLog oa f).map Sigma.fst) :
    d ∈ (tableQueryLog oa f').map Sigma.fst := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp at hd
  | query_bind t k ih =>
    rw [tableQueryLog_query_bind, List.map_cons, List.mem_cons] at hd ⊢
    by_cases htd : d = t
    · exact Or.inl htd
    · right
      rw [h t (Ne.symm htd)]
      exact ih (f t) (hd.resolve_left htd)

/-- **Updating the table at a cell the computation does not query changes nothing.** -/
theorem tableQueryLog_update_of_not_mem (oa : OracleComp (ofFn R) α) (f : ∀ d, R d) (d : D)
    (u : R d) (h : d ∉ (tableQueryLog oa f).map Sigma.fst) :
    evalWithAnswerFn (QueryImpl.ofFn (Function.update f d u)) oa =
        evalWithAnswerFn (QueryImpl.ofFn f) oa ∧
      tableQueryLog oa (Function.update f d u) = tableQueryLog oa f := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [tableQueryLog_query_bind, List.map_cons, List.mem_cons, not_or] at h
    have ht : Function.update f d u t = f t := Function.update_of_ne (Ne.symm h.1) _ _
    obtain ⟨h1, h2⟩ := ih (f t) h.2
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply,
      tableQueryLog_query_bind, ht]
    exact ⟨h1, by rw [h2]⟩

/-- **A queried cell stays queried** when the table is updated there (the log before its first
query does not read it). -/
theorem mem_tableQueryLog_update (oa : OracleComp (ofFn R) α) (f : ∀ d, R d) (d : D) (u : R d)
    (h : d ∈ (tableQueryLog oa f).map Sigma.fst) :
    d ∈ (tableQueryLog oa (Function.update f d u)).map Sigma.fst := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp at h
  | query_bind t k ih =>
    rw [tableQueryLog_query_bind, List.map_cons, List.mem_cons] at h ⊢
    by_cases htd : d = t
    · exact Or.inl htd
    · right
      have ht : Function.update f d u t = f t := Function.update_of_ne (Ne.symm htd) _ _
      rw [ht]
      exact ih (f t) (h.resolve_left htd)

end Log

/-! ## Byte facts -/

lemma extract_push_of_le (A : ByteArray) (b : UInt8) {i j : ℕ} (hj : j ≤ A.size) :
    (A.push b).extract i j = A.extract i j := by
  rw [← ByteArray.append_toByteArray_singleton, ByteArray.extract_append]
  have : j - A.size = 0 := by omega
  rw [this, (ByteArray.extract_eq_empty_iff (b := [b].toByteArray) (i := i - A.size)
    (j := 0)).2 (by simp), ByteArray.append_empty]

lemma extract_zero_append_push (A B : ByteArray) (b : UInt8) {n : ℕ} (hn : A.size = n) :
    ((A ++ B).push b).extract 0 n = A := by
  subst hn
  rw [extract_push_of_le _ _ (by simp), ByteArray.extract_append_eq_left rfl]

lemma extract_mid_append_push (A B C : ByteArray) (b : UInt8) {a n : ℕ} (ha : A.size = a)
    (hn : B.size = n) : ((A ++ (B ++ C)).push b).extract a (a + n) = B := by
  subst ha hn
  rw [extract_push_of_le _ _ (by simp)]
  have h := ByteArray.extract_append_size_add (a := A) (b := B ++ C) (i := 0) (j := B.size)
  rw [Nat.add_zero] at h
  rw [h, ByteArray.extract_append_eq_left rfl]

lemma foldl_append_eq (hs : List ByteArray) (acc : ByteArray) :
    hs.foldl (· ++ ·) acc = acc ++ hs.foldl (· ++ ·) ByteArray.empty := by
  induction hs generalizing acc with
  | nil => simp
  | cons h hs ih =>
    simp only [List.foldl_cons]
    rw [ih (acc ++ h), ih (ByteArray.empty ++ h), ByteArray.empty_append, ByteArray.append_assoc]

lemma size_foldl_append (hs : List ByteArray) (hsz : ∀ h ∈ hs, h.size = 32) :
    (hs.foldl (· ++ ·) ByteArray.empty).size = 32 * hs.length := by
  induction hs with
  | nil => simp
  | cons h hs ih =>
    rw [List.foldl_cons, foldl_append_eq, ByteArray.size_append, ByteArray.empty_append,
      ih fun h' hh => hsz h' (List.mem_cons_of_mem _ hh), hsz h List.mem_cons_self,
      List.length_cons]
    ring

/-- Block `i` of a concatenation of 32-byte strings is the `i`-th string. -/
lemma extract_foldl_append (hs : List ByteArray) (hsz : ∀ h ∈ hs, h.size = 32) {i : ℕ}
    (hi : i < hs.length) :
    (hs.foldl (· ++ ·) ByteArray.empty).extract (32 * i) (32 * i + 32) = hs[i] := by
  induction hs generalizing i with
  | nil => simp at hi
  | cons h hs ih =>
    rw [List.foldl_cons, foldl_append_eq, ByteArray.empty_append]
    have hh : h.size = 32 := hsz h List.mem_cons_self
    cases i with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
      rw [← hh, ByteArray.extract_append_eq_left rfl]
    | succ i =>
      simp only [List.getElem_cons_succ]
      rw [show 32 * (i + 1) = h.size + 32 * i by rw [hh]; ring,
        show h.size + 32 * i + 32 = h.size + (32 * i + 32) by ring,
        ByteArray.extract_append_size_add]
      exact ih (fun h' hh' => hsz h' (List.mem_cons_of_mem _ hh')) (by simp at hi; omega)

/-- **The answers that are bytes of a list**: at most its length out of `2^{8n}`. -/
theorem prEvent_ba_mem_le (n : ℕ) (l : List ByteArray) :
    Pr{let u ← $ᵗ (Bytes n)}[u.ba ∈ l] ≤ (l.length : ℝ≥0∞) / 2 ^ (8 * n) := by
  classical
  rw [SampleableType.prEvent_uniformSample, card_bytes, Nat.cast_pow, Nat.cast_ofNat]
  gcongr
  have h : #{u : Bytes n | u.ba ∈ l} ≤ l.length :=
    (Finset.card_le_card_of_injOn (fun u : Bytes n => u.ba)
      (fun u hu => by simpa using hu) Bytes.ba_injective.injOn).trans (List.toFinset_card_le l)
  exact_mod_cast h

/-! ## The chain inputs in the verifier's log -/

variable [HasPrg]

omit [HasPrg] in
lemma tableQueryLog_mapM_hashQ (g : Table) (k : Kind) (l : List ByteArray) :
    tableQueryLog (l.mapM (hashQ k)) g = l.map fun x => (⟨(k, x), g (k, x)⟩ : (d : Dom) × Ans d) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.mapM_cons, tableQueryLog_bind, tableQueryLog_hashQ, ih, List.map_cons,
      tableQueryLog_pure, List.append_nil, List.cons_append, List.nil_append]

/-- **On an accepted proof, the verifier's leaf-hash and `com` queries are in its log.** -/
theorem inLog_verifyQ_h1 (g : Table) (T : CrtTables) (st : Statement) (proof : ByteArray)
    (h : (verify (Hashes.ofTable g) T st proof).accept = true) {leaves : BAVC.Leaves}
    (hr : BAVC.reconstruct (ivOf (Hashes.ofTable g) ⟨st.params, proof⟩
      (st.mu1 (Hashes.ofTable g))) (Proof.opening ⟨st.params, proof⟩)
      (Proof.delta ⟨st.params, proof⟩) = some leaves) :
    (∀ w ∈ BAVC.leafHashInputs leaves.coms, InLog (verifyQ T st proof) g (.h1, w)) ∧
      InLog (verifyQ T st proof) g (.h1, BAVC.comInput
        ((BAVC.leafHashInputs leaves.coms).map ((Hashes.ofTable g).hash .h1))) := by
  obtain ⟨hf, leaves', hr', -, -⟩ := (accept_iff _ T st proof).1 h
  rw [hr] at hr'
  cases hr'
  simp only [ivOf] at hr
  unfold InLog verifyQ
  refine ⟨fun w hw => ?_, ?_⟩ <;>
  simp only [hf, Bool.not_true, Bool.false_eq_true, ite_false, tableQueryLog_bind,
    evalWithAnswerFn_mu1Q, tableQueryLog_hashQ, evalWithAnswerFn_hashQ, hr,
    evalWithAnswerFn_mapM_hashQ, tableQueryLog_mapM_hashQ, List.map_append, List.map_cons,
    List.mem_append, List.mem_cons, List.map_map]
  · exact Or.inr (Or.inr (Or.inl (List.mem_map.2 ⟨w, hw, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl trivial))))

/-! ## The bad answers -/

/-- The inputs of the queries of kind `k` in a list of queries. -/
def kindIns (k : Kind) (L : List Dom) : List ByteArray := (L.filter fun d => d.1 = k).map Prod.snd

omit [HasPrg] in
lemma mem_kindIns {k : Kind} {L : List Dom} {x : ByteArray} (h : (k, x) ∈ L) : x ∈ kindIns k L :=
  List.mem_map.2 ⟨(k, x), List.mem_filter.2 ⟨h, by simp⟩, rfl⟩

/-- **The targets of a bad answer of kind `k`**, given the prover's queries `L` and its proof's
`Δ`: the 32-byte blocks of its `H₁` inputs and the `com` fields of its `H₂¹` inputs (`H₁`), the
`chal1` fields of its `H₂²` inputs (`H₂¹`), the `chal2` fields of its `H₂³` inputs (`H₂²`), `Δ`
(`H₂³`). -/
def ladderTargets (δ : ByteArray) (L : List Dom) : Kind → List ByteArray
  | .h1 => (kindIns .h1 L).flatMap (fun w => (List.range 17).map fun i =>
        w.extract (32 * i) (32 * i + 32)) ++ (kindIns .h21 L).map (·.extract 32 64)
  | .h21 => (kindIns .h22 L).map (·.extract 0 136)
  | .h22 => (kindIns .h23 L).map (·.extract 0 56)
  | .h23 => [δ]
  | _ => []

/-- **A bad answer**: at a cell the prover did not query, a target of `ladderTargets`. -/
def ladderBad (PQ : Table → List Dom) (δ : Table → ByteArray) (t : Dom) (g : Table) : Prop :=
  t ∉ PQ g ∧ (g t).ba ∈ ladderTargets (δ g) (PQ g) t.1

/-- The kinds of the chain. -/
def ladderKinds : Finset Kind := {.h1, .h21, .h22, .h23}

/-- The bound of a bad answer of each kind. -/
noncomputable def ladderEps (q' : Kind → ℕ) : Kind → ℝ≥0∞
  | .h1 => ((17 * q' .h1 + q' .h21 : ℕ) : ℝ≥0∞) / 2 ^ 256
  | .h21 => (q' .h22 : ℝ≥0∞) / 2 ^ 1088
  | .h22 => (q' .h23 : ℝ≥0∞) / 2 ^ 448
  | .h23 => 1 / 2 ^ 128
  | _ => 0

omit [HasPrg] in
lemma ladderEps_eq_zero (q' : Kind → ℕ) : ∀ k ∉ ladderKinds, ladderEps q' k = 0 := by
  intro k hk
  cases k <;> simp_all [ladderKinds, ladderEps]

omit [HasPrg] in
lemma ladderTargets_of_not_mem (δ : ByteArray) (L : List Dom) {k : Kind} (hk : k ∉ ladderKinds) :
    ladderTargets δ L k = [] := by
  cases k <;> simp_all [ladderKinds, ladderTargets]

omit [HasPrg] in
lemma length_ladderTargets_le (δ : ByteArray) (L : List Dom) (q' : Kind → ℕ)
    (hcnt : ∀ k, (kindIns k L).length ≤ q' k) (k : Kind) :
    ((ladderTargets δ L k).length : ℝ≥0∞) / 2 ^ (8 * k.outLen) ≤ ladderEps q' k := by
  cases k
  case h1 =>
    have hn : (ladderTargets δ L .h1).length ≤ 17 * q' .h1 + q' .h21 := by
      simp only [ladderTargets, List.length_append, List.length_flatMap, List.length_map,
        List.length_range, List.map_const', List.sum_replicate, smul_eq_mul]
      have := hcnt .h1
      have := hcnt .h21
      nlinarith
    simp only [ladderEps, Kind.outLen]
    gcongr
  case h21 =>
    have hn := hcnt .h22
    simp only [ladderTargets, ladderEps, List.length_map, Kind.outLen]
    gcongr
  case h22 =>
    have hn := hcnt .h23
    simp only [ladderTargets, ladderEps, List.length_map, Kind.outLen]
    gcongr
  case h23 => simp [ladderTargets, ladderEps, Kind.outLen]
  all_goals simp [ladderTargets, ladderEps]

variable {β : Type}

/-- **A leaf-hash input of the accepted proof's opening was not queried**: for the opening's leaves
at the verifier's `iv`, some leaf-hash input `c_i ‖ 1` is not among the queries `L`. -/
def LeafUnqueried (st : Statement) (L : List Dom) (r : Out β) : Prop :=
  ∃ leaves, BAVC.reconstruct r.2.2.iv (Proof.opening ⟨st.params, r.1⟩)
      (Proof.delta ⟨st.params, r.1⟩) = some leaves ∧
    ∃ w ∈ BAVC.leafHashInputs leaves.coms, ((.h1, w) : Dom) ∉ L

/-- The verifier's `H₂³` input, read off the output (`chal2` and the check value are in the
transcript). -/
def zOut (st : Statement) (r : Out β) : ByteArray :=
  (r.2.2.chal2 ++ r.2.2.qsCheck ++ (Proof.qsProof ⟨st.params, r.1⟩) ++
    (Proof.ctr ⟨st.params, r.1⟩)).push 11

/-- **On an accepted proof, the `H₂³` input read off the transcript is the verifier's.** -/
lemma zOut_eq_runZ (Hs : Hashes) (T : CrtTables) (st : Statement) (proof : ByteArray)
    (e : ExtData β) (h : (verify Hs T st proof).accept = true) {leaves : BAVC.Leaves}
    (hr : BAVC.reconstruct (ivOf Hs ⟨st.params, proof⟩ (st.mu1 Hs)) (Proof.opening ⟨st.params, proof⟩)
      (Proof.delta ⟨st.params, proof⟩) = some leaves) (keys : ℕ → ℕ → ByteArray) :
    zOut st (proof, e, verify Hs T st proof) = runZ st (runChain Hs T st proof leaves keys) := by
  revert h
  simp only [zOut, runZ, chal3Input, runChain, Chain.pf, verify, Id.run]
  split
  · simp_all
  · simp only [hr]
    split_ifs <;> simp_all [pure]

omit [HasPrg] in
lemma size_mu1 (Hs : Hashes) (hHs : ∀ k x, (Hs.hash k x).size = k.outLen) (st : Statement) :
    (st.mu1 Hs).size = 32 := by
  unfold Statement.mu1 mu
  split <;> simp [hHs, Kind.outLen]

/-- **The walk up the chain** (deterministic, at a table `g`): if the verifier accepts a proof one
of whose leaf-hash inputs the prover did not query, then either the prover did not query the
verifier's `H₂³` input either, or one of the verifier's `H₁`, `H₂¹`, `H₂²` queries is a bad
answer. -/
theorem ladder_walk (T : CrtTables) (st : Statement)
    (oa : OracleComp spec (ByteArray × ExtData β)) (qs : β → List Dom) (g : Table)
    (hacc : (evalWithAnswerFn (QueryImpl.ofFn g) (game T st oa)).2.2.accept = true)
    (hL : LeafUnqueried st (qs (evalWithAnswerFn (QueryImpl.ofFn g) oa).2.aux)
      (evalWithAnswerFn (QueryImpl.ofFn g) (game T st oa))) :
    ((.h23, zOut st (evalWithAnswerFn (QueryImpl.ofFn g) (game T st oa))) : Dom) ∉
        qs (evalWithAnswerFn (QueryImpl.ofFn g) oa).2.aux ∨
      ∃ e ∈ tableQueryLog (game T st oa) g, e.1.1 ≠ .h23 ∧
        ladderBad (fun g => qs (evalWithAnswerFn (QueryImpl.ofFn g) oa).2.aux)
          (fun g => Proof.delta ⟨st.params, (evalWithAnswerFn (QueryImpl.ofFn g) oa).1⟩) e.1 g := by
  set Hs := Hashes.ofTable g
  set π := (evalWithAnswerFn (QueryImpl.ofFn g) oa).1
  set PQ := qs (evalWithAnswerFn (QueryImpl.ofFn g) oa).2.aux
  rw [evalWithAnswerFn_game] at hacc hL ⊢
  obtain ⟨leaves', hr', w, hw, hwq⟩ := hL
  simp only at hacc hr' hwq
  have hacc' := hacc
  obtain ⟨-, leaves, hr, h0, h3⟩ := (accept_iff _ T st π).1 hacc'
  obtain ⟨hiv, -⟩ := verify_iv_chal1 _ T st π hacc hr
  rw [hiv, hr] at hr'
  have e := Option.some.inj hr'
  subst e
  -- The verifier's chain.
  have hHs : ∀ k x, (Hs.hash k x).size = k.outLen := fun k x => by simp [Hs]
  set ch := runChain Hs T st π leaves (fun _ _ => ByteArray.empty)
  obtain ⟨hx, hy, hz⟩ := inLog_verifyQ g T st π hacc hr (fun _ _ => ByteArray.empty)
  obtain ⟨hws, hcw⟩ := inLog_verifyQ_h1 g T st π hacc hr
  have hlog : ∀ t, InLog (verifyQ T st π) g t → ∃ e ∈ tableQueryLog (game T st oa) g, e.1 = t :=
    fun t ht => by
      obtain ⟨e, he, het⟩ := List.mem_map.1 (inLog_game ht)
      exact ⟨e, he, het⟩
  have hbad : ∀ t, InLog (verifyQ T st π) g t → t.1 ≠ .h23 → t ∉ PQ →
      (g t).ba ∈ ladderTargets (Proof.delta ⟨st.params, π⟩) PQ t.1 →
      ((.h23, zOut st (π, (evalWithAnswerFn (QueryImpl.ofFn g) oa).2,
          verify (Hashes.ofTable g) T st π)) : Dom) ∉ PQ ∨
      ∃ e ∈ tableQueryLog (game T st oa) g, e.1.1 ≠ .h23 ∧
        ladderBad (fun g => qs (evalWithAnswerFn (QueryImpl.ofFn g) oa).2.aux)
          (fun g => Proof.delta ⟨st.params, (evalWithAnswerFn (QueryImpl.ofFn g) oa).1⟩) e.1 g :=
    fun t ht hk htq htt => by
      obtain ⟨e, he, rfl⟩ := hlog t ht
      exact Or.inr ⟨e, he, hk, htq, htt⟩
  set lh := (BAVC.leafHashInputs leaves.coms).map (Hs.hash .h1)
  set cw := BAVC.comInput lh
  set com := Hs.hash .h1 cw
  set x := runX Hs st π leaves
  set y := runY Hs st ch
  set z := runZ st ch
  -- z: if the prover did not query it, the first alternative.
  by_cases hzq : ((.h23, z) : Dom) ∉ PQ
  · left
    rwa [zOut_eq_runZ _ T st π _ hacc hr (fun _ _ => ByteArray.empty)]
  rw [not_not] at hzq
  -- y: `chal2` is the first 56 bytes of `z`.
  by_cases hyq : ((.h22, y) : Dom) ∉ PQ
  · refine hbad _ hy (by simp) hyq ?_
    simp only [ladderTargets]
    refine List.mem_map.2 ⟨z, mem_kindIns hzq, ?_⟩
    have hc2 : (g (.h22, y)).ba = ch.chal2 := rfl
    rw [hc2]
    simp only [z, runZ, chal3Input, ByteArray.append_assoc]
    exact extract_zero_append_push _ _ _ (by simp [ch, runChain, chal2, hHs, Kind.outLen])
  rw [not_not] at hyq
  -- x: `chal1` is the first 136 bytes of `y`.
  by_cases hxq : ((.h21, x) : Dom) ∉ PQ
  · refine hbad _ hx (by simp) hxq ?_
    simp only [ladderTargets]
    refine List.mem_map.2 ⟨y, mem_kindIns hyq, ?_⟩
    have hc1 : (g (.h21, x)).ba = ch.chal1 := rfl
    rw [hc1]
    simp only [y, runY, chal2Input, ByteArray.append_assoc]
    exact extract_zero_append_push _ _ _ (by simp [ch, runChain, chal1, hHs, Kind.outLen])
  rw [not_not] at hxq
  -- cw: `com` is bytes 32 … 64 of `x`.
  by_cases hcq : ((.h1, cw) : Dom) ∉ PQ
  · refine hbad _ hcw (by simp) hcq ?_
    simp only [ladderTargets, List.mem_append]
    refine Or.inr (List.mem_map.2 ⟨x, mem_kindIns hxq, ?_⟩)
    have hm : (st.mu1 Hs).size = 32 := size_mu1 Hs hHs st
    have hcs : com.size = 32 := hHs _ _
    show (x.extract 32 (32 + 32)) = com
    simp only [x, runX, chal1Input, BAVC.check, ByteArray.append_assoc]
    exact extract_mid_append_push _ _ _ _ hm hcs
  rw [not_not] at hcq
  -- w: its hash is block `i` of `cw`.
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
  have hlen : (BAVC.leafHashInputs leaves.coms).length = 17 := length_leafHashInputs _
  refine hbad _ (hws _ hw) (by simp) hwq ?_
  simp only [ladderTargets, List.mem_append]
  refine Or.inl (List.mem_flatMap.2 ⟨cw, mem_kindIns hcq, List.mem_map.2 ⟨i,
    List.mem_range.2 (by omega), ?_⟩⟩)
  have hsz : ∀ h ∈ lh, h.size = 32 := fun h hh => by
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 hh
    exact hHs _ _
  have hlh : lh.length = 17 := by simp [lh, hlen]
  show cw.extract (32 * i) (32 * i + 32) = _
  simp only [cw, BAVC.comInput]
  rw [extract_push_of_le _ _ (by rw [size_foldl_append lh hsz, hlh]; omega),
    extract_foldl_append lh hsz (by omega)]
  simp [lh, Hs]

/-- **The walk up the chain**, with the `H₂³` step: the verifier's `H₂³` answer at an input the
prover did not query is the proof's `Δ`, a bad answer too. -/
theorem exists_ladderBad (T : CrtTables) (st : Statement)
    (oa : OracleComp spec (ByteArray × ExtData β)) (qs : β → List Dom) (g : Table)
    (hacc : (evalWithAnswerFn (QueryImpl.ofFn g) (game T st oa)).2.2.accept = true)
    (hL : LeafUnqueried st (qs (evalWithAnswerFn (QueryImpl.ofFn g) oa).2.aux)
      (evalWithAnswerFn (QueryImpl.ofFn g) (game T st oa))) :
    ∃ e ∈ tableQueryLog (game T st oa) g,
      ladderBad (fun g => qs (evalWithAnswerFn (QueryImpl.ofFn g) oa).2.aux)
        (fun g => Proof.delta ⟨st.params, (evalWithAnswerFn (QueryImpl.ofFn g) oa).1⟩) e.1 g := by
  rcases ladder_walk T st oa qs g hacc hL with hz | ⟨e, he, -, hb⟩
  · set π := (evalWithAnswerFn (QueryImpl.ofFn g) oa).1
    rw [evalWithAnswerFn_game] at hacc hz
    obtain ⟨-, leaves, hr, -, h3⟩ := (accept_iff _ T st π).1 hacc
    rw [zOut_eq_runZ _ T st π _ hacc hr (fun _ _ => ByteArray.empty)] at hz
    obtain ⟨-, -, hzl⟩ := inLog_verifyQ g T st π hacc hr (fun _ _ => ByteArray.empty)
    obtain ⟨e, he, hee⟩ := List.mem_map.1 (inLog_game hzl)
    refine ⟨e, he, ?_⟩
    rw [hee]
    refine ⟨hz, ?_⟩
    simp only [ladderTargets, List.mem_singleton]
    exact h3
  · exact ⟨e, he, hb⟩

/-- **The verifier's chain queries were made by the prover, except with small probability**: the
verifier accepts and one of its leaf-hash inputs is not among the prover's reported queries
`qs aux` with probability at most

    (q₁+18)·(17q'₁+q'₂₁)·2⁻²⁵⁶ + (q₂₁+1)·q'₂₂·2⁻¹⁰⁸⁸ + (q₂₂+1)·q'₂₃·2⁻⁴⁴⁸ + (q₂₃+1)·2⁻¹²⁸,

for a prover `oa` with per-domain counts `q` whose reported queries behave as its log (`hfix`,
`hmem`) and number at most `q' k` per kind `k` (`hcnt`). -/
theorem prEvent_accept_leafUnqueried_le (T : CrtTables) (st : Statement)
    (oa : OracleComp spec (ByteArray × ExtData β)) (q : Kind → ℕ) (hq : IsKindQueryBound oa q)
    (qs : β → List Dom) (q' : Kind → ℕ)
    (hfix : ∀ (g : Table) (d : Dom) (u : Ans d), d.1 ∈ ladderKinds →
      d ∉ qs (evalWithAnswerFn (QueryImpl.ofFn g) oa).2.aux →
      evalWithAnswerFn (QueryImpl.ofFn (Function.update g d u)) oa =
        evalWithAnswerFn (QueryImpl.ofFn g) oa)
    (hmem : ∀ (g : Table) (d : Dom) (u : Ans d), d ∈ qs (evalWithAnswerFn (QueryImpl.ofFn g) oa).2.aux →
      d ∈ qs (evalWithAnswerFn (QueryImpl.ofFn (Function.update g d u)) oa).2.aux)
    (hcnt : ∀ (g : Table) k, (kindIns k (qs (evalWithAnswerFn (QueryImpl.ofFn g) oa).2.aux)).length ≤
      q' k) :
    Pr{let r ← (simulateQ randomOracle (game T st oa)).run' ∅}[
        r.2.2.accept = true ∧ LeafUnqueried st (qs r.2.1.aux) r] ≤
      (q .h1 + 18) * ladderEps q' .h1 + (q .h21 + 1) * ladderEps q' .h21 +
        (q .h22 + 1) * ladderEps q' .h22 + (q .h23 + 1) * ladderEps q' .h23 := by
  classical
  set PQ : Table → List Dom := fun g => qs (evalWithAnswerFn (QueryImpl.ofFn g) oa).2.aux
  set δ : Table → ByteArray := fun g =>
    Proof.delta ⟨st.params, (evalWithAnswerFn (QueryImpl.ofFn g) oa).1⟩
  have hbad : ∀ (t : Dom) (g : Table),
      Pr{let u ← $ᵗ (Ans t)}[ladderBad PQ δ t (Function.update g t u)] ≤ ladderEps q' t.1 := by
    rintro ⟨k, w⟩ g
    by_cases ht : ((k, w) : Dom) ∈ PQ g
    · refine (prEvent_mono _ _ (fun _ => False) fun u hu => hu.1 (hmem g _ u ht)).trans ?_
      simp
    by_cases hk : k ∈ ladderKinds
    · have hfx : ∀ u : Ans (k, w), evalWithAnswerFn (QueryImpl.ofFn (Function.update g (k, w) u)) oa =
          evalWithAnswerFn (QueryImpl.ofFn g) oa := fun u => hfix g _ u hk ht
      refine (prEvent_mono _ _ (fun u : Bytes k.outLen => u.ba ∈ ladderTargets (δ g) (PQ g) k)
        fun u hu => ?_).trans ((prEvent_ba_mem_le k.outLen _).trans
          (length_ladderTargets_le (δ g) (PQ g) q' (hcnt g) k))
      have h2 := hu.2
      simp only [PQ, δ, hfx, Function.update_self] at h2
      exact h2
    · refine (prEvent_mono _ _ (fun _ => False) fun u hu => ?_).trans (by simp)
      have h2 := hu.2
      rw [ladderTargets_of_not_mem _ _ hk] at h2
      exact List.not_mem_nil h2
  have htrace : ∀ g : Table, (fun r : Out β => r.2.2.accept = true ∧ LeafUnqueried st (qs r.2.1.aux) r)
      (evalWithAnswerFn (QueryImpl.ofFn g) (game T st oa)) →
      ∃ e ∈ tableQueryLog (game T st oa) g, ladderBad PQ δ e.1 g := by
    intro g h
    have e : (evalWithAnswerFn (QueryImpl.ofFn g) (game T st oa)).2.1 =
        (evalWithAnswerFn (QueryImpl.ofFn g) oa).2 := by rw [evalWithAnswerFn_game]
    obtain ⟨hacc, hL⟩ := h
    rw [e] at hL
    exact exists_ladderBad T st oa qs g hacc hL
  refine (prEvent_exists_bad_query_le (game T st oa) (q + verifierQueries)
    (isKindQueryBound_game T st hq) _ (ladderBad PQ δ) ladderKinds (ladderEps q')
    (ladderEps_eq_zero q') hbad htrace).trans_eq ?_
  simp [ladderKinds, verifierQueries, Pi.add_apply, add_assoc]

/-- The chain kinds below `H₂³`. -/
def ladderKinds' : Finset Kind := {.h1, .h21, .h22}

/-- **The hash ladder without its last step**: the verifier accepts, one of its leaf-hash inputs
is not among the prover's queries, but its `H₂³` input is, with probability at most

    (q₁+18)·(17q'₁+q'₂₁)·2⁻²⁵⁶ + (q₂₁+1)·q'₂₂·2⁻¹⁰⁸⁸ + (q₂₂+1)·q'₂₃·2⁻⁴⁴⁸.

(The case of an `H₂³` input the prover did not query is a single fresh guess,
`ROM/FreshGuess.lean`.) -/
theorem prEvent_accept_leafUnqueried_z_le (T : CrtTables) (st : Statement)
    (oa : OracleComp spec (ByteArray × ExtData β)) (q : Kind → ℕ) (hq : IsKindQueryBound oa q)
    (qs : β → List Dom) (q' : Kind → ℕ)
    (hfix : ∀ (g : Table) (d : Dom) (u : Ans d), d.1 ∈ ladderKinds →
      d ∉ qs (evalWithAnswerFn (QueryImpl.ofFn g) oa).2.aux →
      evalWithAnswerFn (QueryImpl.ofFn (Function.update g d u)) oa =
        evalWithAnswerFn (QueryImpl.ofFn g) oa)
    (hmem : ∀ (g : Table) (d : Dom) (u : Ans d), d ∈ qs (evalWithAnswerFn (QueryImpl.ofFn g) oa).2.aux →
      d ∈ qs (evalWithAnswerFn (QueryImpl.ofFn (Function.update g d u)) oa).2.aux)
    (hcnt : ∀ (g : Table) k, (kindIns k (qs (evalWithAnswerFn (QueryImpl.ofFn g) oa).2.aux)).length ≤
      q' k) :
    Pr{let r ← (simulateQ randomOracle (game T st oa)).run' ∅}[
        r.2.2.accept = true ∧ LeafUnqueried st (qs r.2.1.aux) r ∧
          ((.h23, zOut st r) : Dom) ∈ qs r.2.1.aux] ≤
      (q .h1 + 18) * ladderEps q' .h1 + (q .h21 + 1) * ladderEps q' .h21 +
        (q .h22 + 1) * ladderEps q' .h22 := by
  classical
  set PQ : Table → List Dom := fun g => qs (evalWithAnswerFn (QueryImpl.ofFn g) oa).2.aux
  set δ : Table → ByteArray := fun g =>
    Proof.delta ⟨st.params, (evalWithAnswerFn (QueryImpl.ofFn g) oa).1⟩
  let bad : Dom → Table → Prop := fun t g => t.1 ≠ .h23 ∧ ladderBad PQ δ t g
  let ε : Kind → ℝ≥0∞ := fun k => if k = .h23 then 0 else ladderEps q' k
  have hε : ∀ k ∉ ladderKinds', ε k = 0 := by
    intro k hk
    cases k <;> simp_all [ladderKinds', ε, ladderEps]
  have hbad : ∀ (t : Dom) (g : Table),
      Pr{let u ← $ᵗ (Ans t)}[bad t (Function.update g t u)] ≤ ε t.1 := by
    rintro ⟨k, w⟩ g
    by_cases h23 : k = .h23
    · refine (prEvent_mono _ _ (fun _ => False) fun u hu => hu.1 h23).trans ?_
      rw [prEvent_false]
      exact bot_le
    have hε' : ε k = ladderEps q' k := ite_eq_right_of_eq_false _ _ (eq_false h23)
    show _ ≤ ε k
    rw [hε']
    by_cases ht : ((k, w) : Dom) ∈ PQ g
    · refine (prEvent_mono _ _ (fun _ => False) fun u hu => hu.2.1 (hmem g _ u ht)).trans ?_
      simp
    by_cases hk : k ∈ ladderKinds
    · have hfx : ∀ u : Ans (k, w), evalWithAnswerFn (QueryImpl.ofFn (Function.update g (k, w) u)) oa =
          evalWithAnswerFn (QueryImpl.ofFn g) oa := fun u => hfix g _ u hk ht
      refine (prEvent_mono _ _ (fun u : Bytes k.outLen => u.ba ∈ ladderTargets (δ g) (PQ g) k)
        fun u hu => ?_).trans ((prEvent_ba_mem_le k.outLen _).trans
          (length_ladderTargets_le (δ g) (PQ g) q' (hcnt g) k))
      have h2 := hu.2.2
      simp only [PQ, δ, hfx, Function.update_self] at h2
      exact h2
    · refine (prEvent_mono _ _ (fun _ => False) fun u hu => ?_).trans (by simp)
      have h2 := hu.2.2
      rw [ladderTargets_of_not_mem _ _ hk] at h2
      exact List.not_mem_nil h2
  have htrace : ∀ g : Table, (fun r : Out β => r.2.2.accept = true ∧
      LeafUnqueried st (qs r.2.1.aux) r ∧ ((.h23, zOut st r) : Dom) ∈ qs r.2.1.aux)
      (evalWithAnswerFn (QueryImpl.ofFn g) (game T st oa)) →
      ∃ e ∈ tableQueryLog (game T st oa) g, bad e.1 g := by
    intro g h
    have e : (evalWithAnswerFn (QueryImpl.ofFn g) (game T st oa)).2.1 =
        (evalWithAnswerFn (QueryImpl.ofFn g) oa).2 := by rw [evalWithAnswerFn_game]
    obtain ⟨hacc, hL, hz⟩ := h
    rw [e] at hL hz
    rcases ladder_walk T st oa qs g hacc hL with hz' | ⟨e, he, hk, hb⟩
    · exact absurd hz hz'
    · exact ⟨e, he, hk, hb⟩
  refine (prEvent_exists_bad_query_le (game T st oa) (q + verifierQueries)
    (isKindQueryBound_game T st hq) _ bad ladderKinds' ε hε hbad htrace).trans_eq ?_
  simp [ladderKinds', verifierQueries, Pi.add_apply, add_assoc, ε]

end VoleMole.ROM
