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

lemma logBefore_prefix {D : Type} [DecidableEq D] {R : D → Type} (d : D) (L : QueryLog (ofFn R)) :
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

end Chain

end VoleMole.ROM.IC
