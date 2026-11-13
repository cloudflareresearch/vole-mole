import VoleMole.ROM.OneMoreLemmaPIC

/-!
# Lemma P's identification: the extraction from a prefix of the prover's log

`lean/docs/security/pomfrit.md` §6.4 (gap G8). The derived prover `proverP … i`
(`ROM/OneMoreLemmaPIC.lean`) runs the forger and then the verifications of the forgeries up to their
target queries, with the cipher as queries. Its joint log is the forger's log `L` followed by the
verification queries `V`. The game extracts from `L`; the adaptive bound of `ROM/LemmaP.lean`
extracts from `L ++ V`. This file shows that, outside the chain hits and Post, the two extractions
agree when the verifier's `H₂³` input is in `L` (generic in the prover):

* `mem_x_of_mem_z`: without hits, the verifier's `H₂¹` input comes before its `H₂²` input, which
  comes before its `H₂³` input, so all three are in `L` if the last one is.
* `extractKey_sandwich`, `keysOf_knownOf_prefix`: the committed keys are found before the
  verifier's `H₂¹` input (`KeysPre`, from no Post), so the extractor finds the same key in any
  log between the log before that input and the whole log: `L`'s keys and known trees are the
  whole log's.
* `aliveR_eq_filter`, `aliveR_subset_known`: the alive trees of the output are the trees with no
  committed dead leaf at the verifier's `H₂¹` input; outside Post and the hits they are known
  (L2(c), `sameChainHyp_ic`).

No `sorry`, no `axiom`.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

/-! ## Searching a prefix -/

section Prefix

lemma find?_eq_of_prefix {α : Type} {p : α → Bool} {A B : List α} (h : A <+: B) {a : α}
    (ha : A.find? p = some a) : B.find? p = some a := by
  obtain ⟨C, rfl⟩ := h
  rw [List.find?_append, ha]; rfl

lemma find?_eq_none_of_prefix {α : Type} {p : α → Bool} {A B : List α} (h : A <+: B)
    (hb : B.find? p = none) : A.find? p = none := by
  cases ha : A.find? p with
  | none => rfl
  | some a => rw [find?_eq_of_prefix h ha] at hb; cases hb

/-- **A search in a log sandwiched between two logs on which it agrees** returns the same. -/
lemma find?_sandwich {α : Type} {p : α → Bool} {A B C : List α} (hAB : A <+: B) (hBC : B <+: C)
    (h : A.find? p = C.find? p) : B.find? p = C.find? p := by
  cases ha : A.find? p with
  | some a => rw [find?_eq_of_prefix hAB ha]; rw [ha] at h; exact h
  | none =>
    rw [ha] at h
    rw [← h]
    exact find?_eq_none_of_prefix hBC h.symm

lemma extractKey_sandwich {A B C : QueryLog cspec} (hAB : A <+: B) (hBC : B <+: C) (E : CTable)
    (iv : ByteArray) (i : ℕ) (a : ByteArray)
    (h : extractKey A E iv i a = extractKey C E iv i a) :
    extractKey B E iv i a = extractKey C E iv i a := by
  unfold extractKey at h ⊢
  -- the searches agree, so the results agree
  by_cases hA : A.find? (fun q => decide ((q.1.2 = lp iv i 0 ∨ q.1.2 = lp iv i 1) ∧
      ba (E (q.1.1, lp iv i 0)) ++ ba (E (q.1.1, lp iv i 1)) = a)) =
      C.find? (fun q => decide ((q.1.2 = lp iv i 0 ∨ q.1.2 = lp iv i 1) ∧
      ba (E (q.1.1, lp iv i 0)) ++ ba (E (q.1.1, lp iv i 1)) = a))
  · rw [find?_sandwich hAB hBC hA]
  · -- the results agree although the searches differ: the first search succeeds in `A`
    cases hfa : A.find? (fun q => decide ((q.1.2 = lp iv i 0 ∨ q.1.2 = lp iv i 1) ∧
        ba (E (q.1.1, lp iv i 0)) ++ ba (E (q.1.1, lp iv i 1)) = a)) with
    | some e =>
      rw [find?_eq_of_prefix hAB hfa]
      rw [hfa] at h; exact h
    | none =>
      rw [hfa] at h hA
      cases hfc : C.find? (fun q => decide ((q.1.2 = lp iv i 0 ∨ q.1.2 = lp iv i 1) ∧
          ba (E (q.1.1, lp iv i 0)) ++ ba (E (q.1.1, lp iv i 1)) = a)) with
      | none => exact absurd hfc.symm hA
      | some e => rw [hfc] at h; simp at h

lemma cipherLog_prefix {A B : QueryLog specIC} (h : A <+: B) : cipherLog A <+: cipherLog B := by
  obtain ⟨C, rfl⟩ := h
  exact ⟨cipherLog C, (List.filterMap_append ..).symm⟩

lemma logBefore_isPrefix {D : Type} [DecidableEq D] {R : D → Type} (d : D) (L : QueryLog (ofFn R)) :
    logBefore d L <+: L :=
  ⟨_, (exists_append_logBefore d L).choose_spec.symm⟩

end Prefix

/-! ## The verifier's chain in a prefix of the prover's log -/

section Chain

variable {β : Type} (T : CrtTables) (st : Statement) (P : OracleComp specIC (ByteArray × β))
  (E : CTable) (g : Table)

lemma hashEnt_prefix {A B : QueryLog specIC} (h : A <+: B) : hashEnt A <+: hashEnt B := by
  obtain ⟨C, rfl⟩ := h
  exact ⟨hashEnt C, (hashEnt_append A C).symm⟩

lemma mem_hashEnt_iff {d : Dom} {L : QueryLog specIC} :
    d ∈ (hashEnt L).map Sigma.fst ↔ d ∈ hashLog L := by
  rw [map_fst_hashEnt]

/-- **Without hits, the verifier's `H₂¹` input is in a prefix of `P`'s log that contains its `H₂³`
input** (the order `x`, `y`, `z` of `chain_ident`). -/
theorem mem_x_of_mem_z (hh : NoHit (gameIC T st P E) (chainHit T st P E) g)
    (keys : ℕ → ℕ → ByteArray)
    (hacc : (@verify (icPrg E.cipher) (Hashes.ofTable g) T st (πOf g P E)).accept = true)
    {leaves : BAVC.Leaves}
    (hr : @BAVC.reconstruct (icPrg E.cipher) (ivE g st P E) (Proof.opening ⟨st.params, πOf g P E⟩)
      (Proof.delta ⟨st.params, πOf g P E⟩) = some leaves)
    {L : QueryLog specIC} (hL : L <+: jOf g P E)
    (hz : ((.h23, runZ st (@runChain (icPrg E.cipher) (Hashes.ofTable g) T st
      (πOf g P E) leaves keys)) : Dom) ∈ hashLog L) :
    ((.h21, runX (Hashes.ofTable g) st (πOf g P E) leaves) : Dom) ∈ hashLog L := by
  let _ : HasPrg := icPrg E.cipher
  obtain ⟨-, -, -, -, hO3, hO4⟩ := chain_ident T st P E g hh keys hacc hr
  obtain ⟨rest, hG⟩ := gLog_eq_hashEnt_append T st P E g
  obtain ⟨V, hV⟩ := hL
  set G := gLog T st P E g
  have hG' : G = hashEnt L ++ (hashEnt V ++ rest) := by
    rw [hG, ← hV, hashEnt_append, List.append_assoc]
  have hz' : ((.h23, runZ st (runChain (Hashes.ofTable g) T st (πOf g P E) leaves keys)) : Dom) ∈
      (hashEnt L).map Sigma.fst := mem_hashEnt_iff.2 hz
  rw [hG', logBefore_append_of_mem _ hz'] at hO4
  have hy : ((.h22, runY (Hashes.ofTable g) st
      (runChain (Hashes.ofTable g) T st (πOf g P E) leaves keys)) : Dom) ∈
      (hashEnt L).map Sigma.fst := by
    obtain ⟨e, he, he1⟩ := List.mem_map.1 hO4
    exact List.mem_map.2 ⟨e, mem_of_mem_logBefore he, he1⟩
  rw [hG', logBefore_append_of_mem _ hy] at hO3
  obtain ⟨e, he, he1⟩ := List.mem_map.1 hO3
  exact mem_hashEnt_iff.1 (List.mem_map.2 ⟨e, mem_of_mem_logBefore he, he1⟩)

/-- **The extraction from a prefix of `P`'s log is the extraction from the whole log** when the
prefix contains the verifier's `H₂¹` input, outside the hits and Post (`KeysPre`): every commitment
the extractor looks up is committed at that input, and its key is found before it. -/
theorem keysOf_knownOf_prefix (hh : NoHit (gameIC T st P E) (chainHit T st P E) g)
    (hkp : KeysPre st E (jOf g P E) (gLog T st P E g) g)
    (hacc : (@verify (icPrg E.cipher) (Hashes.ofTable g) T st (πOf g P E)).accept = true)
    {leaves : BAVC.Leaves}
    (hr : @BAVC.reconstruct (icPrg E.cipher) (ivE g st P E) (Proof.opening ⟨st.params, πOf g P E⟩)
      (Proof.delta ⟨st.params, πOf g P E⟩) = some leaves)
    {L : QueryLog specIC} (hL : L <+: jOf g P E)
    (hx : ((.h21, runX (Hashes.ofTable g) st (πOf g P E) leaves) : Dom) ∈ hashLog L) :
    keysOf (cipherLog L) E (ivE g st P E) (Proof.opening ⟨st.params, πOf g P E⟩)
        (Proof.delta ⟨st.params, πOf g P E⟩) =
      keysOf (cipherLog (jOf g P E)) E (ivE g st P E) (Proof.opening ⟨st.params, πOf g P E⟩)
        (Proof.delta ⟨st.params, πOf g P E⟩) ∧
    knownOf (cipherLog L) E (ivE g st P E) (Proof.opening ⟨st.params, πOf g P E⟩) =
      knownOf (cipherLog (jOf g P E)) E (ivE g st P E) (Proof.opening ⟨st.params, πOf g P E⟩) := by
  let _ : HasPrg := icPrg E.cipher
  obtain ⟨hf, leaves', hr0, -⟩ := (accept_iff _ T st (πOf g P E)).1 hacc
  have hHs : ∀ k w, ((Hashes.ofTable g).hash k w).size = k.outLen := fun k w => by simp
  obtain ⟨hcom, hwH, -⟩ := chain_ident T st P E g hh (fun _ _ => ByteArray.empty) hacc hr
  set x := runX (Hashes.ofTable g) st (πOf g P E) leaves
  have hivX : ivX st x g = ivE g st P E := by
    simp only [x, ivX, ivE, ivOf, runX]
    rw [xIvPre_chal1Input hf (size_mu1 _ hHs st) (hHs _ _)]
  have hxmu : x.extract 0 32 = st.mu1 (Hashes.ofTable g) := by
    simp only [x, runX]
    exact extract_mu_chal1Input (size_mu1 _ hHs st)
  -- the sandwich of cipher logs
  obtain ⟨V, hV⟩ := hL
  have hxL : (.inl (.h21, x) : DomIC) ∈ L.map Sigma.fst := mem_hashLog.1 hx
  have hB : logBefore (.inl (.h21, x)) (jOf g P E) = logBefore (.inl (.h21, x)) L := by
    rw [← hV]; exact logBefore_append_of_mem _ hxL
  have hAB : cipherLog (logBefore (.inl (.h21, x)) (jOf g P E)) <+: cipherLog L := by
    rw [hB]; exact cipherLog_prefix (logBefore_isPrefix _ _)
  have hBC : cipherLog L <+: cipherLog (jOf g P E) := cipherLog_prefix ⟨V, hV⟩
  have key : ∀ i < BAVC.tau, ∀ j < 2 ^ BAVC.kOf i,
      extractKey (cipherLog L) E (ivE g st P E) i (comAt leaves.coms i j) =
        extractKey (cipherLog (jOf g P E)) E (ivE g st P E) i (comAt leaves.coms i j) := by
    intro i hi j hj
    have h := hkp x hxmu i hi j hj _ (hcom i hi j hj) (fun hxJ => hwH hxJ i hi j hj)
    rw [hivX] at h
    exact extractKey_sandwich hAB hBC E _ i _ h
  refine ⟨?_, ?_⟩
  · funext i j
    by_cases hv : i < BAVC.tau ∧ j < 2 ^ BAVC.kOf i
    · rw [keysOf_of_reconstruct hr hv.1 hv.2, keysOf_of_reconstruct hr hv.1 hv.2, key i hv.1 j hv.2]
    · rw [keysOf_of_not_valid _ _ _ _ _ hv, keysOf_of_not_valid _ _ _ _ _ hv]
  · ext i
    simp only [knownOf, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← comAt_reconstruct_hidden hr i.isLt,
      key i i.isLt _ (show BAVC.deltaIndex _ i < 2 ^ BAVC.kOf i from hiddenIndex_lt _ _)]

lemma firstIn_isSome {k : Kind} {ok : ByteArray → Bool} {a : ByteArray} {L : QueryLog spec}
    {e : (t : Dom) × Ans t} (he : e ∈ L) (hk : e.1.1 = k) (hok : ok e.1.2 = true)
    (ha : (e.2 : Ans e.1).ba = a) : (firstIn k ok a L).isSome := by
  unfold firstIn
  rw [Option.isSome_map]
  exact List.find?_isSome.2 ⟨e, he, by simp [hk, hok, ha]⟩

/-- **The alive trees of the output are the trees with no committed dead leaf** at the verifier's
`H₂¹` input, when `P` queried that input, without hits. -/
theorem aliveR_eq_filter (hh : NoHit (gameIC T st P E) (chainHit T st P E) g)
    (hacc : (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)).2.2.accept = true)
    {leaves : BAVC.Leaves}
    (hr : @BAVC.reconstruct (icPrg E.cipher) (ivE g st P E) (Proof.opening ⟨st.params, πOf g P E⟩)
      (Proof.delta ⟨st.params, πOf g P E⟩) = some leaves)
    (hx : ((.h21, runX (Hashes.ofTable g) st (πOf g P E) leaves) : Dom) ∈ hashLog (jOf g P E)) :
    aliveR E (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)) =
      univ.filter fun i => deadOf T st P E g i = ∅ := by
  classical
  let _ : HasPrg := icPrg E.cipher
  set r := evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)
  set Hs := Hashes.ofTable g
  set π := πOf g P E
  have hr2 : r.2.2 = verify Hs T st π := by
    simp only [r, gameIC]
    rw [evalWithAnswerFn_game, proverIC_fst]
    rfl
  have hJ : r.2.1.aux.2 = jOf g P E := aux_gameIC T st P E g
  rw [hr2] at hacc
  obtain ⟨hf, leaves', hrec, -⟩ := (accept_iff _ T st π).1 hacc
  have hrec' : BAVC.reconstruct (ivE g st P E) (Proof.opening ⟨st.params, π⟩)
      (Proof.delta ⟨st.params, π⟩) = some leaves' := hrec
  rw [hr] at hrec'
  cases hrec'
  obtain ⟨hiv, hc1⟩ := verify_iv_chal1 _ T st π hacc hrec
  have hdead : deadOf T st P E g = deadAtX T st P E (runX Hs st π leaves) g := by
    unfold deadOf; rw [hr]
  rw [hdead]
  obtain ⟨rest, hG⟩ := gLog_eq_hashEnt_append T st P E g
  have hxH : ((.h21, runX Hs st π leaves) : Dom) ∈ (hashEnt (jOf g P E)).map Sigma.fst :=
    mem_hashEnt_iff.2 hx
  have hlog : logBefore (.h21, runX Hs st π leaves) (gLog T st P E g) =
      logBefore (.h21, runX Hs st π leaves) (hashEnt (jOf g P E)) := by
    rw [hG]; exact logBefore_append_of_mem rest hxH
  have hivX : ivX st (runX Hs st π leaves) g = (verify Hs T st π).iv := by
    rw [hiv]
    unfold ivX ivOf runX
    rw [xIvPre_chal1Input hf]
    · exact size_mu1 Hs (fun k w => by simp [Hs]) st
    · exact Prob.Bytes.size_ba _
  -- the first `H₂¹` preimage of `chal1` in `P`'s log is the verifier's input
  have hfirst : firstIn .h21 (fun _ => true) r.2.2.chal1 (hashEnt r.2.1.aux.2) =
      some (runX Hs st π leaves) := by
    rw [hJ, hr2, hc1]
    obtain ⟨e, he, he1⟩ := List.mem_map.1 hxH
    have hsub : ∀ e ∈ hashEnt (jOf g P E), e ∈ gLog T st P E g := fun e he => by
      rw [hG]; exact List.mem_append_left _ he
    exact firstIn_gLog T st P E g hh (Or.inr (Or.inl rfl)) (d := (.h21, runX Hs st π leaves)) rfl
      hsub hxH rfl
  unfold aliveR
  rw [hfirst]
  dsimp only
  rw [hJ, hr2]
  unfold deadAtX
  rw [hlog, hivX]

/-- **Outside Post and the hits, the alive trees are known** (L2(c)), when `P` queried the
verifier's `H₂¹` input. -/
theorem aliveR_subset_known (hh : NoHit (gameIC T st P E) (chainHit T st P E) g)
    (hpost : ¬PostOut E (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)))
    (hacc : (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)).2.2.accept = true)
    {leaves : BAVC.Leaves}
    (hr : @BAVC.reconstruct (icPrg E.cipher) (ivE g st P E) (Proof.opening ⟨st.params, πOf g P E⟩)
      (Proof.delta ⟨st.params, πOf g P E⟩) = some leaves)
    (hx : ((.h21, runX (Hashes.ofTable g) st (πOf g P E) leaves) : Dom) ∈ hashLog (jOf g P E)) :
    aliveR E (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)) ⊆
      (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)).2.1.known := by
  intro i hi
  rw [aliveR_eq_filter T st P E g hh hacc hr hx, Finset.mem_filter] at hi
  by_contra hk
  have hs := sameChainHyp_ic T st P E g hacc hpost hh
  have hr' : @BAVC.reconstruct (icPrg E.cipher)
      (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)).2.2.iv
      (Proof.opening ⟨st.params, (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)).1⟩)
      (Proof.delta ⟨st.params, (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)).1⟩) =
      some leaves := by
    have e1 := gameIC_fst T st P g E
    have etr := gameIC_tr T st P g E
    have hacc' := hacc
    rw [etr] at hacc' ⊢
    rw [e1]
    obtain ⟨-, leaves', hrec, -⟩ := (@accept_iff (icPrg E.cipher) _ T st (πOf g P E)).1 hacc'
    rw [(@verify_iv_chal1 (icPrg E.cipher) _ T st _ hacc' _ hrec).1]
    exact hr
  have := (hs leaves hr').2 i hk
  rw [hi.2] at this
  exact Finset.not_nonempty_empty this

end Chain

end VoleMole.ROM.IC
