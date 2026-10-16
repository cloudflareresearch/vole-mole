import VoleMole.ROM.AdaptGame

/-!
# Statement binding: the statement read off the log (plan M6, L4 (H-stmt))

For a non-delayed statement the verifier's `H₂¹` input begins with `mu₁ = H₂⁰(inst ‖ DST ‖ 8)`
(`chal1Input`), so the chain committed at an `H₂¹` query determines the statement, provided the
`H₂⁰` preimage of its first 32 bytes was queried *before* and is the only one. Here:

* `xMu x`: the `mu₁` field of an `H₂¹` input; `muIn st`: the `H₂⁰` input `inst ‖ DST ‖ 8` of a
  (non-delayed) statement.
* **The statement committed at a chain query** (`stmtAt dec L t`), read off the log `L` before `t`
  only: at an `H₂¹` input `x`, the decoding (`dec`) of the first `H₂⁰` input in the log before `x`
  whose answer is `xMu x` (`sX`); at an `H₂²` input `y`, the statement at the first `H₂¹`
  preimage of its `chal1` (`sY`); at an `H₂³` input `z`, the statement at the first `H₂²`
  preimage of its `chal2` (`sZ`). It does not read the table at `t` (`stmtAt_update`).
* **Statement hits** (`stmtHit`): an `H₂⁰` answer equal to the `mu₁` field of an earlier `H₂¹`
  input, or to an earlier `H₂⁰` answer (`stmtTargets`). Per `H₂⁰` query, probability
  `≤ (n₂₁ + n₀)·2⁻²⁵⁶` for a computation with `n k` queries of kind `k` (`prEvent_stmtHit_le`).
* **The identification** (`stmtAt_ident`): in the fixed game at a non-delayed statement `st`
  with `dec (muIn st) = some s`, on an accepted proof without chain hits (`chainHit`) and without
  statement hits, the statement committed at each of the verifier's `H₂¹`, `H₂²`, `H₂³` inputs is
  `s`: the extractor queried `muIn st` (`mu_mem_gLog`), whose answer is `xMu x`; it was queried
  before `x` (else a statement hit at `muIn st`) and it is the only `H₂⁰` input before `x` with
  that answer (else a collision, a statement hit at the later one); the `H₂²` and `H₂³` inputs
  lead to `x` by `chain_ident`.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

/-! ## The statement's `mu₁` in the chain's inputs -/

/-- The `mu₁` field of an `H₂¹` input: its first 32 bytes. -/
def xMu (x : ByteArray) : ByteArray := x.extract 0 32

lemma xMu_chal1Input {pf : Proof} {mu1 com b1 : ByteArray} (hmu : mu1.size = 32) :
    xMu (chal1Input pf mu1 com b1) = mu1 := by
  simp only [xMu, chal1Input, ByteArray.append_assoc]
  exact extract_zero_append_push _ _ _ hmu

/-- **The `H₂⁰` input of a statement**: `inst ‖ DST ‖ 8` (the instance encoding at the empty
`chal1`, as `Statement.mu1` reads it without delayed binding). -/
def muIn (st : Statement) : ByteArray := (st.instEnc ByteArray.empty ++ st.dst).push 8

lemma mu1_ofTable {st : Statement} (hd : st.delayed = false) (g : Table) :
    st.mu1 (Hashes.ofTable g) = (g (.mu, muIn st)).ba := by
  simp [Statement.mu1, hd, mu, muIn]

/-! ## Statement hits -/

/-- **The targets of a statement hit**, given the log `pre` before the hit's cell: the `mu₁`
fields of the earlier `H₂¹` inputs and the earlier `H₂⁰` answers. -/
def stmtTargets (pre : QueryLog spec) : List ByteArray :=
  (kindIns .h21 (pre.map Sigma.fst)).map xMu ++ ansOf .mu pre

/-- **A statement hit**: an `H₂⁰` answer that is a target of the log `L g` before its cell. -/
def stmtHit (L : Table → QueryLog spec) (t : Dom) (g : Table) : Prop :=
  t.1 = .mu ∧ (g t).ba ∈ stmtTargets (logBefore t (L g))

/-- The bound of a statement hit, for a computation with `n k` queries of kind `k`. -/
noncomputable def stmtEps (n : Kind → ℕ) : Kind → ℝ≥0∞
  | .mu => ((n .h21 + n .mu : ℕ) : ℝ≥0∞) / 2 ^ 256
  | _ => 0

lemma stmtEps_eq_zero (n : Kind → ℕ) {k : Kind} (hk : k ≠ .mu) : stmtEps n k = 0 := by
  cases k <;> simp_all [stmtEps]

/-- **A statement hit has probability `≤ (n₂₁ + n₀)·2⁻²⁵⁶` when its cell alone is resampled.** -/
theorem prEvent_stmtHit_le {α : Type} (oa : OracleComp spec α) (n : Kind → ℕ)
    (hn : IsKindQueryBound oa n) (t : Dom) (g : Table) :
    Pr{let u ← $ᵗ (Ans t)}[stmtHit (tableQueryLog oa) t (Function.update g t u)] ≤
      stmtEps n t.1 := by
  obtain ⟨k, x⟩ := t
  by_cases hk : k = .mu
  · subst hk
    have h : ∀ u : Ans (.mu, x), stmtHit (tableQueryLog oa) (.mu, x) (Function.update g (.mu, x) u) ↔
        u.ba ∈ stmtTargets (logBefore (.mu, x) (tableQueryLog oa g)) := fun u => by
      simp only [stmtHit, Function.update_self, logBefore_tableQueryLog_update, true_and]
    simp_rw [h]
    refine (prEvent_ba_mem_le Kind.mu.outLen _).trans ?_
    have hc : ∀ k, (kindIns k ((logBefore (.mu, x) (tableQueryLog oa g)).map Sigma.fst)).length ≤
        n k := fun k =>
      (length_kindIns_le_of_sublist ((logBefore_sublist _ _).map _)).trans
        (length_kindIns_tableQueryLog_le _ hn g k)
    have hl : (stmtTargets (logBefore (.mu, x) (tableQueryLog oa g))).length ≤ n .h21 + n .mu := by
      simp only [stmtTargets, List.length_append, List.length_map, length_ansOf]
      have := hc .h21; have := hc .mu; omega
    simp only [stmtEps, Kind.outLen]
    gcongr
  · refine (prEvent_mono _ _ (fun _ => False) fun u hu => hk hu.1).trans ?_
    rw [prEvent_false]
    exact bot_le

/-! ## The statement committed at a chain query -/

section Stmt

variable {ι : Type} (dec : ByteArray → Option ι)

/-- The statement committed at an `H₂¹` input `x`, from the log `G` before `x`: the decoded first
`H₂⁰` preimage of `xMu x`. -/
def sX (G : QueryLog spec) (x : ByteArray) : Option ι :=
  (firstIn .mu (fun _ => true) (xMu x) G).bind dec

/-- The statement committed at an `H₂²` input `y`: that at the first `H₂¹` preimage of its
`chal1`. -/
def sY (G : QueryLog spec) (y : ByteArray) : Option ι :=
  match firstIn .h21 (fun _ => true) (yChal1 y) G with
  | some x => sX dec (logBefore (.h21, x) G) x
  | none => none

/-- The statement committed at an `H₂³` input `z`: that at the first `H₂²` preimage of its
`chal2`. -/
def sZ (G : QueryLog spec) (z : ByteArray) : Option ι :=
  match firstIn .h22 (fun _ => true) (zChal2 z) G with
  | some y => sY dec (logBefore (.h22, y) G) y
  | none => none

/-- **The statement committed at the query `t`**, read off the log `L` before `t`. -/
def stmtAt (L : QueryLog spec) (t : Dom) : Option ι :=
  match t.1 with
  | .h21 => sX dec (logBefore t L) t.2
  | .h22 => sY dec (logBefore t L) t.2
  | .h23 => sZ dec (logBefore t L) t.2
  | _ => none

/-- **The statement committed at `t` does not read the table at `t`.** -/
theorem stmtAt_update {α : Type} (oa : OracleComp spec α) (g : Table) (t : Dom) (u : Ans t) :
    stmtAt dec (tableQueryLog oa (Function.update g t u)) t = stmtAt dec (tableQueryLog oa g) t := by
  unfold stmtAt
  rw [logBefore_tableQueryLog_update]

end Stmt

/-! ## The extractor's `H₂⁰` query -/

section MuLog

variable {β : Type} (T : CrtTables) (st : Statement) (P : OracleComp specIC (ByteArray × β))
  (E : CTable) (g : Table)

/-- **The extractor queries the statement's `H₂⁰` input** (non-delayed statements). -/
theorem mu_mem_gLog (hd : st.delayed = false) :
    ((.mu, muIn st) : Dom) ∈ (gLog T st P E g).map Sigma.fst := by
  unfold gLog
  rw [gameIC_eq_bind, tableQueryLog_bind, proverIC_eq_bind, tableQueryLog_bind]
  simp only [List.map_append, List.mem_append]
  refine Or.inl (Or.inr ?_)
  simp only [extractIC, mu1Q, hd, Bool.false_eq_true, ite_false]
  rw [tableQueryLog_bind, tableQueryLog_hashQ]
  simp [muIn]

end MuLog

/-! ## The identification -/

section Ident

variable {ι β : Type} (dec : ByteArray → Option ι) (T : CrtTables) (st : Statement)
  (P : OracleComp specIC (ByteArray × β)) (E : CTable) (g : Table)

/-- No statement hit in the fixed game's log. -/
def NoStmtHit : Prop := ∀ e ∈ gLog T st P E g, ¬stmtHit (gLog T st P E) e.1 g

/-- Without statement hits, two `H₂⁰` cells of the game's log with the same answer are equal. -/
lemma mu_cell_eq (hs : NoStmtHit T st P E g) {a b : Dom}
    (ha : a ∈ (gLog T st P E g).map Sigma.fst) (hb : b ∈ (gLog T st P E g).map Sigma.fst)
    (hka : a.1 = .mu) (hkb : b.1 = .mu) (hans : (g a).ba = (g b).ba) : a = b := by
  by_contra hab
  have key : ∀ c d : Dom, d.1 = .mu → c ∈ (logBefore d (gLog T st P E g)).map Sigma.fst →
      c.1 = .mu → (g c).ba = (g d).ba → d ∈ (gLog T st P E g).map Sigma.fst → False := by
    intro c d hd hc hck hcd hdG
    have he := exists_entry (fun e he => gLog_answer T st P E g e (mem_of_mem_logBefore he)) hc
    have hmem : (g d).ba ∈ stmtTargets (logBefore d (gLog T st P E g)) := by
      rw [← hcd]
      simp only [stmtTargets, List.mem_append]
      exact Or.inr (List.mem_map.2 ⟨_, List.mem_filter.2 ⟨he, by simp [hck]⟩, rfl⟩)
    obtain ⟨e, heG, rfl⟩ := List.mem_map.1 hdG
    exact hs e heG ⟨hd, hmem⟩
  rcases mem_or_mem_logBefore ha hb hab with h | h
  · exact key a b hkb h hka hans hb
  · exact key b a hka h hkb hans.symm ha

/-- **The statement committed at the verifier's `H₂¹` input is the verifier's**, without
statement hits: `muIn st` was queried before `x`, and it is the first `H₂⁰` preimage of `xMu x`
there. -/
theorem sX_ident (hd : st.delayed = false) {s : ι} (hdec : dec (muIn st) = some s)
    (hs : NoStmtHit T st P E g) {x : ByteArray}
    (hxG : ((.h21, x) : Dom) ∈ (gLog T st P E g).map Sigma.fst)
    (hxmu : xMu x = (g (.mu, muIn st)).ba) :
    sX dec (logBefore (.h21, x) (gLog T st P E g)) x = some s := by
  set G := gLog T st P E g
  have hmuG := mu_mem_gLog T st P E g hd
  have hO : ((.mu, muIn st) : Dom) ∈ (logBefore (.h21, x) G).map Sigma.fst := by
    refine (mem_or_mem_logBefore hmuG hxG (by simp)).resolve_right fun h => ?_
    obtain ⟨e, heG, he1⟩ := List.mem_map.1 hmuG
    refine hs e heG ⟨by rw [he1], ?_⟩
    rw [he1, ← hxmu]
    simp only [stmtTargets, List.mem_append]
    exact Or.inl (List.mem_map.2 ⟨x, mem_kindIns h, rfl⟩)
  have hsub : ∀ e ∈ logBefore (.h21, x) G, e ∈ G := fun e he => mem_of_mem_logBefore he
  have hF : firstIn .mu (fun _ => true) (xMu x) (logBefore (.h21, x) G) = some (muIn st) := by
    refine firstIn_eq ⟨⟨(.mu, muIn st), g (.mu, muIn st)⟩,
      exists_entry (fun e he => gLog_answer T st P E g e (hsub e he)) hO, rfl, hxmu.symm⟩ rfl
      fun e he hek _ hea => ?_
    have heG := hsub e he
    rw [ans_of_mem_gLog T st P E g heG, hxmu] at hea
    have := mu_cell_eq T st P E g hs (List.mem_map.2 ⟨e, heG, rfl⟩) hmuG hek rfl hea
    rw [this]
  rw [sX, hF, Option.bind_some, hdec]

/-- **The identification**: in the fixed game at a non-delayed statement `st` with
`dec (muIn st) = some s`, on an accepted proof without chain hits and statement hits, the
statement committed at the verifier's `H₂¹`, `H₂²` and `H₂³` inputs is `s`. -/
theorem stmtAt_ident (hd : st.delayed = false) {s : ι} (hdec : dec (muIn st) = some s)
    (hh : NoHit (gameIC T st P E) (chainHit T st P E) g) (hs : NoStmtHit T st P E g)
    (keys : ℕ → ℕ → ByteArray) : letI := icPrg E.cipher
    (verify (Hashes.ofTable g) T st (πOf g P E)).accept = true → ∀ {leaves : BAVC.Leaves},
    BAVC.reconstruct (ivE g st P E) (Proof.opening ⟨st.params, πOf g P E⟩)
      (Proof.delta ⟨st.params, πOf g P E⟩) = some leaves →
    let ch := runChain (Hashes.ofTable g) T st (πOf g P E) leaves keys
    let G := gLog T st P E g
    stmtAt dec G (.h21, runX (Hashes.ofTable g) st (πOf g P E) leaves) = some s ∧
      stmtAt dec G (.h22, runY (Hashes.ofTable g) st ch) = some s ∧
      stmtAt dec G (.h23, runZ st ch) = some s := by
  let _ : HasPrg := icPrg E.cipher
  intro hacc leaves hr
  dsimp only
  obtain ⟨-, -, hF3, hF4, hO3, hO4⟩ := chain_ident T st P E g hh keys hacc hr
  have hr0 : BAVC.reconstruct (ivOf (Hashes.ofTable g) ⟨st.params, πOf g P E⟩
      (st.mu1 (Hashes.ofTable g))) (Proof.opening ⟨st.params, πOf g P E⟩)
      (Proof.delta ⟨st.params, πOf g P E⟩) = some leaves := hr
  obtain ⟨hxL, -, -⟩ := inLog_verifyQ g T st (πOf g P E) hacc hr0 keys
  have hxG := inLog_gLog T st P E g hxL
  have hHs : ∀ k w, ((Hashes.ofTable g).hash k w).size = k.outLen := fun k w => by simp
  have hxmu : xMu (runX (Hashes.ofTable g) st (πOf g P E) leaves) = (g (.mu, muIn st)).ba := by
    rw [runX, xMu_chal1Input (size_mu1 _ hHs st), mu1_ofTable hd]
  have h1 := sX_ident dec T st P E g hd hdec hs hxG hxmu
  have h2 : sY dec (logBefore (.h22, runY (Hashes.ofTable g) st
      (runChain (Hashes.ofTable g) T st (πOf g P E) leaves keys)) (gLog T st P E g))
      (runY (Hashes.ofTable g) st
        (runChain (Hashes.ofTable g) T st (πOf g P E) leaves keys)) = some s := by
    rw [sY, hF3]
    dsimp only
    rw [logBefore_logBefore hO3]
    exact h1
  refine ⟨h1, h2, ?_⟩
  show sZ dec (logBefore (.h23, runZ st (runChain (Hashes.ofTable g) T st (πOf g P E) leaves keys))
    (gLog T st P E g)) (runZ st (runChain (Hashes.ofTable g) T st (πOf g P E) leaves keys)) = some s
  rw [sZ, hF4]
  dsimp only
  rw [logBefore_logBefore hO4]
  exact h2

end Ident

end VoleMole.ROM.IC
