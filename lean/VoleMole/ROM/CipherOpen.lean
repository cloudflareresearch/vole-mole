import VoleMole.ROM.FreshGuess

/-!
# No dead leaf is opened (plan M6, `ε_open`)

`ROM/CipherGame.lean` bounds the binding failure in the joint hash and ideal-cipher experiment by
`2·q_E²·2⁻²⁵⁶ + ε_open`, with `ε_open = Pr[DeadOpenOut]`: the verifier accepts, and some non-hidden
leaf of its reconstruction has a key `s'` that the prover queried at neither of the leaf's two
points `x₀`, `x₁`. Here `ε_open` is bounded explicitly (`prEvent_joint_deadOpen_le`):

    Pr[DeadOpenOut] ≤ (q₁+18)·(17q₁+q₂₁)·2⁻²⁵⁶ + (q₂₁+1)·q₂₂·2⁻¹⁰⁸⁸ + (q₂₂+1)·q₂₃·2⁻⁴⁴⁸
      + 2⁻¹²⁸ + q₁·2⁻²⁵⁶.

The proof splits on the leaf hash `w_i = c_i ‖ 1` of the dead leaf's tree.

* **`w_i` was not queried by the prover** (`LeafUnqueried`): the hash ladder of
  `ROM/Queried.lean`, at every cipher table, for the prover `proverIC st E P` with its own hash
  queries read off its joint log (`hashLog`). If `P` queried the verifier's `H₂³` input, some
  verifier query below it is a hit (`prEvent_accept_leafUnqueried_z_le`, union bound); if not,
  acceptance is one fresh guess of `Δ` (`prEvent_accept_zUnqueried_le`, `ROM/FreshGuess.lean`,
  `2⁻¹²⁸`, not charged to every `H₂³` query). This is `L0-L2`'s linking L1.4 (`Hit₁`, and its
  analogues up the chain) in the form "the verifier's queries were the prover's".
* **`w_i` was queried** (`deadQueried`): then the prover's `H₁` input `w_i` contains, as its block
  `j`, the commitment `E_{s'}(x₀) ‖ E_{s'}(x₁)` of the dead leaf, two cipher values at cells the
  prover never queried. For a fixed hash table this is a guess of two fresh cipher cells
  (`prEvent_two_cells_le`, a resampling argument: updating the table at the two cells changes
  neither the prover's run, nor the verifier's leaf key `s'` (the GGM derivation reads only the
  cells of tweak `< L − 1`, `recTree_ic_congr_cells`), nor the dead leaf), with at most `q₁`
  targets: `≤ q₁·2⁻²⁵⁶` (`prEvent_deadQueried_le`). This is `L0-L2`'s L2(a) for leaves with no
  key evaluated at all (the verifier's key there is never evaluated by the prover).

Together with `ROM/CipherGame.lean`: **`moussakaIssue_accept_le_ic'`**, the Moussaka issuance bound
in the joint experiment with `ε_bind` fully explicit,

    (q₁+1)·2⁻¹⁵⁰ + (q₂+1)·ε_QS(4008) + (Q+1)·9·2⁻¹²⁸ + 2·q_E²·2⁻²⁵⁶ + ε_open(q) + ε_dead + ε_chain
      + Σ_k q'_k·εh_k

(the last three are discharged in `ROM/CipherFull.lean`, `moussakaIssue_accept_le_full`).
-/

open Finset OracleComp OracleSpec
open MeasureTheory
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim
open VoleMole.EndToEnd VoleMole.SeedExtraction VoleMole.ROM

/-! ## The joint log -/

section Log

variable {α : Type}

@[simp] lemma hashLog_nil : hashLog [] = [] := rfl

@[simp] lemma hashLog_cons_inl (d : Dom) (u : Ans d) (l : QueryLog specIC) :
    hashLog (⟨.inl d, u⟩ :: l) = d :: hashLog l := rfl

@[simp] lemma hashLog_cons_inr (x : Cell) (u : Blk) (l : QueryLog specIC) :
    hashLog (⟨.inr x, u⟩ :: l) = hashLog l := rfl

lemma mem_hashLog {l : QueryLog specIC} {d : Dom} :
    d ∈ hashLog l ↔ (.inl d : DomIC) ∈ l.map Sigma.fst := by
  induction l with
  | nil => simp
  | cons e l ih =>
    obtain ⟨t, u⟩ := e
    cases t with
    | inl d' =>
      show d ∈ d' :: hashLog l ↔ (Sum.inl d : DomIC) ∈ (Sum.inl d') :: l.map Sigma.fst
      rw [List.mem_cons, List.mem_cons, ih, Sum.inl.injEq]
    | inr x =>
      show d ∈ hashLog l ↔ (Sum.inl d : DomIC) ∈ (Sum.inr x) :: l.map Sigma.fst
      rw [List.mem_cons, ih]
      exact ⟨Or.inr, fun h => h.resolve_left Sum.inl_ne_inr⟩

lemma mem_cipherLog {l : QueryLog specIC} {x : Cell} :
    x ∈ (cipherLog l).map Sigma.fst ↔ (.inr x : DomIC) ∈ l.map Sigma.fst := by
  induction l with
  | nil => simp
  | cons e l ih =>
    obtain ⟨t, u⟩ := e
    cases t with
    | inl d =>
      show x ∈ (cipherLog l).map Sigma.fst ↔ (Sum.inr x : DomIC) ∈ (Sum.inl d) :: l.map Sigma.fst
      rw [List.mem_cons, ih]
      exact ⟨Or.inr, fun h => h.resolve_left Sum.inr_ne_inl⟩
    | inr x' =>
      show x ∈ x' :: (cipherLog l).map Sigma.fst ↔
        (Sum.inr x : DomIC) ∈ (Sum.inr x') :: l.map Sigma.fst
      rw [List.mem_cons, List.mem_cons, ih, Sum.inr.injEq]

@[simp] lemma join_inl (g : Table) (E : CTable) (d : Dom) : join g E (.inl d) = g d := rfl

@[simp] lemma join_inr (g : Table) (E : CTable) (x : Cell) : join g E (.inr x) = E x := rfl

lemma join_update_inl_of_ne (g : Table) (E : CTable) (d : Dom) (u : Ans d) {t : DomIC}
    (ht : t ≠ .inl d) : join (Function.update g d u) E t = join g E t := by
  cases t with
  | inl d' => exact Function.update_of_ne (fun h => ht (by rw [h])) _ _
  | inr x => rfl

lemma join_update_inr_of_ne (g : Table) (E : CTable) (x : Cell) (v : Blk) {t : DomIC}
    (ht : t ≠ .inr x) : join g (Function.update E x v) t = join g E t := by
  cases t with
  | inl d => rfl
  | inr x' => exact Function.update_of_ne (fun h => ht (by rw [h])) _ _

lemma kindIns_cons (k : Kind) (d : Dom) (L : List Dom) :
    kindIns k (d :: L) = if d.1 = k then d.2 :: kindIns k L else kindIns k L := by
  unfold kindIns
  by_cases h : d.1 = k <;> simp [h]

/-- **`P`'s hash queries per kind** are within its budget. -/
theorem length_kindIns_hashLog_le (P : OracleComp specIC α) {q : Kind → ℕ}
    (hq : IsKindQueryBoundIC P q) (f : (t : DomIC) → AnsIC t) (k : Kind) :
    (kindIns k (hashLog (tableQueryLog P f))).length ≤ q k := by
  induction P using OracleComp.inductionOn generalizing q with
  | pure a => simp [kindIns]
  | query_bind t k' ih =>
    rw [IsKindQueryBoundIC, isQueryBound_query_bind_iff] at hq
    rw [tableQueryLog_query_bind]
    cases t with
    | inl d =>
      have h : (kindIns k (hashLog (tableQueryLog (k' (f (.inl d))) f))).length ≤
          Function.update q d.1 (q d.1 - 1) k := ih (f (.inl d)) (hq.2 (f (.inl d)))
      show (kindIns k (d :: hashLog _)).length ≤ q k
      rw [kindIns_cons]
      have h0 : 0 < q d.1 := hq.1
      by_cases hk : d.1 = k
      · subst hk
        simp only [↓reduceIte, List.length_cons]
        rw [Function.update_self] at h
        omega
      · simp only [hk, ↓reduceIte]
        rwa [Function.update_of_ne (Ne.symm hk)] at h
    | inr x => exact ih (f (.inr x)) (hq.2 (f (.inr x)))

end Log

/-! ## The prover's hash queries behave as a log -/

section Prover

variable {β : Type}

lemma hash_ofTable_update_of_ne (g : Table) (d : Dom) (u : Ans d) {k : Kind} (hk : k ≠ d.1)
    (x : ByteArray) : (Hashes.ofTable (Function.update g d u)).hash k x = (Hashes.ofTable g).hash k x := by
  simp only [Hashes.ofTable_hash]
  rw [Function.update_of_ne (fun h => hk (congrArg Prod.fst h))]

lemma ne_of_mem_ladderKinds {k : Kind} (hk : k ∈ ladderKinds) :
    Kind.h4 ≠ k ∧ Kind.mu ≠ k ∧ Kind.muDelayed ≠ k := by
  simp only [ladderKinds, Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl <;> decide

/-- `P`'s output and joint log against the hash table `g`. -/
lemma proverIC_fst (g : Table) (st : Statement) (E : CTable) (P : OracleComp specIC (ByteArray × β)) :
    (evalWithAnswerFn (QueryImpl.ofFn g) (proverIC st E P)).1 =
      (evalWithAnswerFn (QueryImpl.ofFn (join g E)) P).1 := by
  rw [evalWithAnswerFn_proverIC]

lemma proverIC_aux (g : Table) (st : Statement) (E : CTable) (P : OracleComp specIC (ByteArray × β)) :
    (evalWithAnswerFn (QueryImpl.ofFn g) (proverIC st E P)).2.aux =
      ((evalWithAnswerFn (QueryImpl.ofFn (join g E)) P).2, tableQueryLog P (join g E)) := by
  rw [evalWithAnswerFn_proverIC]

/-- **Updating the hash table at a chain cell the prover did not query changes nothing** in
`proverIC` (its hash queries are `P`'s, the extractor's `mu₁` and `iv` are of other kinds). -/
theorem proverIC_update (g : Table) (st : Statement) (E : CTable)
    (P : OracleComp specIC (ByteArray × β)) (d : Dom) (u : Ans d) (hk : d.1 ∈ ladderKinds)
    (hd : d ∉ hashLog (tableQueryLog P (join g E))) :
    evalWithAnswerFn (QueryImpl.ofFn (Function.update g d u)) (proverIC st E P) =
      evalWithAnswerFn (QueryImpl.ofFn g) (proverIC st E P) := by
  obtain ⟨h4, hmu, hmuD⟩ := ne_of_mem_ladderKinds hk
  have hP := tableQueryLog_congr P (join g E) (join (Function.update g d u) E) fun t ht =>
    join_update_inl_of_ne g E d u fun h => mem_hashLog.not.1 hd (h ▸ ht)
  have hH : tableQueryLog (runH (Function.update g d u) P) E = tableQueryLog (runH g P) E := by
    rw [← cipherLog_tableQueryLog, ← cipherLog_tableQueryLog, hP.2]
  rw [evalWithAnswerFn_proverIC, evalWithAnswerFn_proverIC]
  simp only [hP.1, hP.2, hH, ivOf, Statement.mu1, mu,
    hash_ofTable_update_of_ne g d u h4, hash_ofTable_update_of_ne g d u hmu,
    hash_ofTable_update_of_ne g d u hmuD]

theorem proverIC_mem (g : Table) (st : Statement) (E : CTable)
    (P : OracleComp specIC (ByteArray × β)) (d : Dom) (u : Ans d)
    (hd : d ∈ hashLog (evalWithAnswerFn (QueryImpl.ofFn g) (proverIC st E P)).2.aux.2) :
    d ∈ hashLog (evalWithAnswerFn (QueryImpl.ofFn (Function.update g d u)) (proverIC st E P)).2.aux.2 := by
  rw [proverIC_aux] at hd ⊢
  rw [mem_hashLog] at *
  exact mem_tableQueryLog_congr P _ _ _ (fun t ht => join_update_inl_of_ne g E d u ht) hd

/-- The bound of the hash ladder for a prover with per-domain counts `q`: the three hits
(`H₁`, `H₂¹`, `H₂²`), each charged to every query of its kind, and the single fresh guess of
the verifier's `H₂³` answer. -/
noncomputable def openHashEps (q : Kind → ℕ) : ℝ≥0∞ :=
  (q .h1 + 18) * ladderEps q .h1 + (q .h21 + 1) * ladderEps q .h21 +
    (q .h22 + 1) * ladderEps q .h22 + (2 ^ 128 : ℝ≥0∞)⁻¹

/-- **The leaf hashes of an accepted proof were queried by `P`**, at every cipher table: the
verifier accepts and one of its leaf-hash inputs is not among `P`'s hash queries with probability
at most `openHashEps q`. Split on the verifier's `H₂³` input: queried by `P`, the ladder below it
(`prEvent_accept_leafUnqueried_z_le`); not queried, one fresh guess (`prEvent_accept_zUnqueried_le`). -/
theorem prEvent_leafUnqueried_ic_le (T : CrtTables) (st : Statement)
    (P : OracleComp specIC (ByteArray × β)) (q : Kind → ℕ) (hq : IsKindQueryBoundIC P q)
    (E : CTable) :
    Pr{let r ← (simulateQ randomOracle (gameIC T st P E)).run' ∅}[
        r.2.2.accept = true ∧ @LeafUnqueried (icPrg E.cipher) _ st (hashLog r.2.1.aux.2) r] ≤
      openHashEps q := by
  let _ : HasPrg := icPrg E.cipher
  have hfix : ∀ (g : Table) (d : Dom) (u : Ans d), d.1 ∈ ladderKinds →
      d ∉ hashLog (evalWithAnswerFn (QueryImpl.ofFn g) (proverIC st E P)).2.aux.2 →
      evalWithAnswerFn (QueryImpl.ofFn (Function.update g d u)) (proverIC st E P) =
        evalWithAnswerFn (QueryImpl.ofFn g) (proverIC st E P) :=
    fun g d u hk hd => proverIC_update g st E P d u hk (by rwa [proverIC_aux] at hd)
  have h1 := prEvent_accept_leafUnqueried_z_le T st (proverIC st E P) (q + extractorQueries)
    (isKindQueryBound_proverIC st E hq) (fun aux => hashLog aux.2) q hfix
    (fun g d u hd => proverIC_mem g st E P d u hd)
    (fun g k => by rw [proverIC_aux]; exact length_kindIns_hashLog_le P hq (join g E) k)
  have h2 := prEvent_accept_zUnqueried_le T st (proverIC st E P) (fun aux => hashLog aux.2) hfix
  have e1 : (q + extractorQueries) .h1 = q .h1 := by simp [extractorQueries]
  have e2 : (q + extractorQueries) .h21 = q .h21 := by simp [extractorQueries]
  have e3 : (q + extractorQueries) .h22 = q .h22 := by simp [extractorQueries]
  rw [e1, e2, e3] at h1
  refine (prEvent_mono _ _ (fun r => (r.2.2.accept = true ∧
      @LeafUnqueried (icPrg E.cipher) _ st (hashLog r.2.1.aux.2) r ∧
        ((.h23, zOut st r) : Dom) ∈ hashLog r.2.1.aux.2) ∨
      (r.2.2.accept = true ∧ ((.h23, zOut st r) : Dom) ∉ hashLog r.2.1.aux.2))
      fun r h => (em (((.h23, zOut st r) : Dom) ∈ hashLog r.2.1.aux.2)).elim
        (fun hz => Or.inl ⟨h.1, h.2, hz⟩) fun hz => Or.inr ⟨h.1, hz⟩).trans
    ((prEvent_or_le _ _ _).trans (add_le_add h1 h2))

end Prover

/-! ## Guessing two fresh cipher cells -/

section TwoCells

/-- The table `E` with the two cells `a`, `b` set to `w`. -/
def upd2 (E : CTable) (a b : Cell) (w : Blk × Blk) : CTable :=
  Function.update (Function.update E a w.1) b w.2

lemma upd2_upd2 (E : CTable) (a b : Cell) (w w' : Blk × Blk) :
    upd2 (upd2 E a b w) a b w' = upd2 E a b w' := by
  funext x
  simp only [upd2, Function.update_apply]
  split_ifs <;> rfl

lemma upd2_self (E : CTable) (a b : Cell) : upd2 E a b (E a, E b) = E := by
  funext x
  simp only [upd2, Function.update_apply]
  split_ifs with h1 h2 <;> simp_all

lemma upd2_apply_fst (E : CTable) {a b : Cell} (hab : a ≠ b) (w : Blk × Blk) :
    upd2 E a b w a = w.1 := by
  simp [upd2, hab]

lemma upd2_apply_snd (E : CTable) (a b : Cell) (w : Blk × Blk) : upd2 E a b w b = w.2 := by
  simp [upd2]

lemma upd2_apply_of_ne (E : CTable) {a b x : Cell} (ha : x ≠ a) (hb : x ≠ b) (w : Blk × Blk) :
    upd2 E a b w x = E x := by
  simp [upd2, ha, hb]

lemma cipher_upd2_of_ne (E : CTable) (a b : Cell) (w : Blk × Blk) (k : Blk) {z : Blk}
    (ha : z ≠ a.2) (hb : z ≠ b.2) : (upd2 E a b w).cipher k z = E.cipher k z :=
  upd2_apply_of_ne E (fun h => ha (congrArg Prod.snd h)) (fun h => hb (congrArg Prod.snd h)) w

/-- **Two fresh cipher cells hit a target set of size `K` with probability at most `K·2⁻²⁵⁶`.**
`ev E` implies that the values of `E` at two different cells `c₁ E`, `c₂ E` form a target in
`T E` (at most `K` of them), and setting the two cells to any values keeps the cells and the
targets (the event is about cells that nothing else of the experiment reads): the class counting
`card_finOf_mul_le` with the two cells as one index. -/
theorem prEvent_two_cells_le (ev : CTable → Prop) (c₁ c₂ : CTable → Cell)
    (T : CTable → Finset (Blk × Blk)) (K : ℕ) (hne : ∀ E, ev E → c₁ E ≠ c₂ E)
    (hinv : ∀ E, ev E → ∀ w, c₁ (upd2 E (c₁ E) (c₂ E) w) = c₁ E ∧
      c₂ (upd2 E (c₁ E) (c₂ E) w) = c₂ E ∧ T (upd2 E (c₁ E) (c₂ E) w) = T E)
    (hK : ∀ E, ev E → (T E).card ≤ K) (hev : ∀ E, ev E → (E (c₁ E), E (c₂ E)) ∈ T E) :
    Pr{let E ← $ᵗ CTable}[ev E] ≤ K * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  have hnat := card_finOf_mul_le (Ω := CTable) (I := Cell × Cell) (W := Blk × Blk)
    (fun E i w => upd2 E i.1 i.2 w) (fun E i => (E i.1, E i.2)) (fun i => i.1 ≠ i.2)
    (fun E i w w' => upd2_upd2 E i.1 i.2 w w') (fun E i => upd2_self E i.1 i.2)
    (fun E i w hi => Prod.ext (upd2_apply_fst E hi w) (upd2_apply_snd E i.1 i.2 w))
    ev (fun E => (c₁ E, c₂ E)) T K hne
    (fun E hE w => ⟨Prod.ext (hinv E hE w).1 (hinv E hE w).2.1, (hinv E hE w).2.2⟩) hK hev
  have hM : Fintype.card (Blk × Blk) = 2 ^ 128 * 2 ^ 128 := by
    rw [Fintype.card_prod, card_blk]
  have hev' : Pr{let E ← $ᵗ CTable}[ev E] = (#(finOf ev) : ℝ≥0∞) / Fintype.card CTable := by
    rw [@SampleableType.prEvent_uniformSample _ _ _ ev (Classical.decPred ev), finOf_eq]
  rw [hev']
  have hN0 : (Fintype.card CTable : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hNt : (Fintype.card CTable : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [ENNReal.div_le_iff hN0 hNt]
  have h2 : (2 ^ 256 : ℝ≥0∞) ≠ 0 := pow_ne_zero _ two_ne_zero
  have h2t : (2 ^ 256 : ℝ≥0∞) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have hcast : (#(finOf ev) : ℝ≥0∞) * 2 ^ 256 ≤ K * Fintype.card CTable := by
    have := (Nat.cast_le (α := ℝ≥0∞)).2 hnat
    rw [Nat.cast_mul, Nat.cast_mul, hM, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      ← pow_add] at this
    exact this
  calc (#(finOf ev) : ℝ≥0∞) = #(finOf ev) * 2 ^ 256 * (2 ^ 256)⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel h2 h2t, mul_one]
    _ ≤ K * Fintype.card CTable * (2 ^ 256)⁻¹ := mul_le_mul_of_nonneg_right hcast (by simp)
    _ = K * (2 ^ 256)⁻¹ * Fintype.card CTable := by ring

end TwoCells

/-! ## The GGM derivation does not read the leaf-commitment cells -/

section GGM

/-- The two points of the GGM expansion of node `n`: the blocks of `PRG(node, iv, tweak = n)`. -/
def gp (iv : ByteArray) (n c : ℕ) : Blk := blk 16 (AES.ctrBlock iv (0 + c.toUInt32) n.toUInt32)

lemma children_ic_congr_cells {E E' : Cipher} {iv node : ByteArray} {n : ℕ}
    (h : ∀ k c, c < 2 → E k (gp iv n c) = E' k (gp iv n c)) :
    @BAVC.children (icPrg E) iv node n = @BAVC.children (icPrg E') iv node n := by
  show icPrgF E node iv n.toUInt32 0 2 = icPrgF E' node iv n.toUInt32 0 2
  unfold icPrgF
  split_ifs with hk
  · rw [prgR_two, prgR_two]
    have h0 := h (blk 16 node) 0 (by norm_num)
    have h1 := h (blk 16 node) 1 (by norm_num)
    simp only [gp] at h0 h1
    rw [h0, h1]
  · rfl

variable {E E' : Cipher} {iv opening delta : ByteArray}

/-- **The derivation reads the table only at the GGM points** (tweaks `< L − 1`). -/
theorem derivedN_ic_congr_cells
    (h : ∀ k, ∀ n < BAVC.numLeaves - 1, ∀ c < 2, E k (gp iv n c) = E' k (gp iv n c)) :
    ∀ N ≤ BAVC.numLeaves - 1,
      @derivedN (icPrg E) iv opening delta N = @derivedN (icPrg E') iv opening delta N := by
  intro N
  induction N with
  | zero => intro _; exact (@derivN_zero (icPrg E) iv _).trans (@derivN_zero (icPrg E') iv _).symm
  | succ N ih =>
    intro hN
    rewrite [@derivedN_succ (icPrg E), @derivedN_succ (icPrg E'), ← ih (by omega)]
    rcases hA : (@derivedN (icPrg E) iv opening delta N)[N]! with _ | node
    · simp only [BAVC.deriveStep, hA]
    · have hc : @BAVC.children (icPrg E) iv node N = @BAVC.children (icPrg E') iv node N :=
        children_ic_congr_cells fun k c hc => h k N (by omega) c hc
      simp only [BAVC.deriveStep, hA, hc]

theorem recTree_ic_congr_cells
    (h : ∀ k, ∀ n < BAVC.numLeaves - 1, ∀ c < 2, E k (gp iv n c) = E' k (gp iv n c)) :
    @recTree (icPrg E) iv opening delta = @recTree (icPrg E') iv opening delta := by
  unfold recTree
  rewrite [derivedN_ic_congr_cells h _ le_rfl]
  rfl

/-- **A leaf-commitment point is no GGM point** (its tweak is `i + L − 1 ≥ L − 1`). -/
lemma lp_ne_gp (iv : ByteArray) {i n : ℕ} (c c' : ℕ) (hi : i < BAVC.tau)
    (hn : n < BAVC.numLeaves - 1) : lp iv i c ≠ gp iv n c' := by
  intro h
  have ht := congrArg UInt32.toNat (blkCtr_inj iv h).2
  have hL : BAVC.numLeaves = 2304 := rfl
  have hτ : BAVC.tau = 17 := rfl
  rw [toNat_toUInt32 (by omega), toNat_toUInt32 (by omega)] at ht
  omega

end GGM

/-! ## The leaf hashes and the commitments -/

section Coms

variable [HasPrg]

omit [HasPrg] in
lemma mem_pieces {f : ℕ → ℕ → ByteArray} {n : ℕ} {b : ByteArray} (h : b ∈ pieces f n) :
    ∃ i < n, ∃ j < 2 ^ BAVC.kOf i, b = f i j := by
  unfold pieces at h
  obtain ⟨i, hi, hb⟩ := List.mem_flatMap.1 h
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hb
  exact ⟨i, List.mem_range.1 hi, j, List.mem_range.1 hj, rfl⟩

/-- **The reconstructed commitments are `32 L` bytes.** -/
lemma reconstruct_coms_size {iv opening delta : ByteArray} {leaves : BAVC.Leaves}
    (h : BAVC.reconstruct iv opening delta = some leaves) :
    leaves.coms.size = 32 * BAVC.numLeaves := by
  rw [reconstruct_eq] at h
  split_ifs at h with hb
  cases h
  rw [Bool.not_eq_true] at hb
  have hsz := (badOpening_false hb).1
  rw [leavesOf_eq]
  simp only
  rw [size_foldl_uniform 32 _ _ fun b hb' => ?_, pieces_length, leafOffset_tau, ByteArray.size_empty,
    Nat.zero_add]
  obtain ⟨i, hi, j, -, rfl⟩ := mem_pieces hb'
  split
  · have h1 : BAVC.openSize = 2224 := rfl
    have h2 : BAVC.hashLen = 32 := rfl
    have h3 : BAVC.tau = 17 := rfl
    rw [ByteArray.size_extract, hsz, h1, h2]
    rw [h3] at hi
    omega
  · rw [BAVC.leafCom, HasPrg.prg_size]

/-- **Block `j` of the leaf-hash input of tree `i` is the commitment of leaf `(i, j)`.** -/
lemma extract_leafHashInput {coms : ByteArray} (hc : coms.size = 32 * BAVC.numLeaves) {i j : ℕ}
    (hi : i < BAVC.tau) (hj : j < 2 ^ BAVC.kOf i) :
    ((BAVC.leafHashInputs coms)[i]'(by rw [length_leafHashInputs]; exact hi)).extract (32 * j)
      (32 * j + 32) = comAt coms i j := by
  simp only [BAVC.leafHashInputs, List.getElem_map, List.getElem_range, BAVC.hashLen]
  have hoff : BAVC.leafOffset i + 2 ^ BAVC.kOf i ≤ BAVC.numLeaves := by
    rw [← leafOffset_succ, ← leafOffset_tau]
    exact leafOffset_mono (by omega)
  rw [extract_push_of_le _ _ (by rw [ByteArray.size_extract, hc]; omega), ByteArray.extract_extract]
  unfold comAt
  congr 1
  · ring
  · rw [Nat.min_eq_left (by omega)]
    ring

end Coms

/-! ## A dead leaf whose leaf hash the prover queried -/

section Dead

variable {β : Type} (g : Table) (st : Statement) (P : OracleComp specIC (ByteArray × β))

/-- `P`'s proof against the hash table `g` and the cipher table `E`. -/
def πOf (E : CTable) : ByteArray := (evalWithAnswerFn (QueryImpl.ofFn (join g E)) P).1

/-- `P`'s joint log. -/
def jOf (E : CTable) : QueryLog specIC := tableQueryLog P (join g E)

/-- The verifier's `iv` on `P`'s proof. -/
def ivE (E : CTable) : ByteArray :=
  ivOf (Hashes.ofTable g) ⟨st.params, πOf g P E⟩ (st.mu1 (Hashes.ofTable g))

/-- The verifier's reconstructed tree, with the ideal cipher `E`. -/
def rtOf (E : CTable) : Array ByteArray :=
  @recTree (icPrg E.cipher) (ivE g st P E) (Proof.opening ⟨st.params, πOf g P E⟩)
    (Proof.delta ⟨st.params, πOf g P E⟩)

/-- **Leaf `p` is dead**: not hidden, and its verifier key was queried by `P` at neither of its
points. -/
def DeadAt (E : CTable) (p : ℕ × ℕ) : Prop :=
  p.1 < BAVC.tau ∧ p.2 < 2 ^ BAVC.kOf p.1 ∧
    p.2 ≠ BAVC.deltaIndex (Proof.delta ⟨st.params, πOf g P E⟩) p.1 ∧
    ¬HasCell (cipherLog (jOf g P E)) (blk 16 (rtOf g st P E)[BAVC.treePos p.1 p.2]!)
      (lp (ivE g st P E) p.1 0) (lp (ivE g st P E) p.1 1)

/-- A dead leaf (if any). -/
noncomputable def deadPt (E : CTable) : ℕ × ℕ := Classical.epsilon (DeadAt g st P E)

/-- Its verifier key. -/
noncomputable def deadKey (E : CTable) : Blk := blk 16 (rtOf g st P E)[BAVC.treePos (deadPt g st P E).1 (deadPt g st P E).2]!

/-- Its two cells. -/
noncomputable def dc (E : CTable) (c : ℕ) : Cell := (deadKey g st P E, lp (ivE g st P E) (deadPt g st P E).1 c)

lemma dc_fst (E : CTable) (c : ℕ) : (dc g st P E c).1 = deadKey g st P E := rfl

lemma dc_snd (E : CTable) (c : ℕ) :
    (dc g st P E c).2 = lp (ivE g st P E) (deadPt g st P E).1 c := rfl

/-- A 32-byte commitment as two blocks. -/
def split32 (a : ByteArray) : Blk × Blk := (blk 16 (a.extract 0 16), blk 16 (a.extract 16 32))

lemma split32_ba (u v : Blk) : split32 (ba u ++ ba v) = (u, v) := by
  unfold split32
  rw [ByteArray.extract_append_eq_left (size_ba u).symm,
    ByteArray.extract_append_eq_right (size_ba u).symm (by rw [size_ba, size_ba]), blk_ba, blk_ba]

/-- The targets: block `j` of each of `P`'s `H₁` inputs, at the dead leaf's `j`. -/
noncomputable def deadTargets (E : CTable) : Finset (Blk × Blk) :=
  ((kindIns .h1 (hashLog (jOf g P E))).map fun w =>
    split32 (w.extract (32 * (deadPt g st P E).2) (32 * (deadPt g st P E).2 + 32))).toFinset

/-- **A dead leaf, with all the leaf hashes queried by `P`.** -/
def DeadQueried (E : CTable) : Prop :=
  (∃ leaves, @BAVC.reconstruct (icPrg E.cipher) (ivE g st P E) (Proof.opening ⟨st.params, πOf g P E⟩)
      (Proof.delta ⟨st.params, πOf g P E⟩) = some leaves ∧
    ∀ w ∈ BAVC.leafHashInputs leaves.coms, ((.h1, w) : Dom) ∈ hashLog (jOf g P E)) ∧
  ∃ p, DeadAt g st P E p

lemma deadAt_deadPt {E : CTable} (h : ∃ p, DeadAt g st P E p) :
    DeadAt g st P E (deadPt g st P E) :=
  Classical.epsilon_spec h

/-- **Setting the dead leaf's two cells changes nothing else**: they are not in `P`'s log (so its
run is the same) and not GGM points (so the verifier's tree is the same). -/
theorem deadQueried_inv {E : CTable} (hE : ∃ p, DeadAt g st P E p) (w : Blk × Blk) :
    dc g st P (upd2 E (dc g st P E 0) (dc g st P E 1) w) 0 = dc g st P E 0 ∧
      dc g st P (upd2 E (dc g st P E 0) (dc g st P E 1) w) 1 = dc g st P E 1 ∧
      deadTargets g st P (upd2 E (dc g st P E 0) (dc g st P E 1) w) = deadTargets g st P E := by
  obtain ⟨hi, -, -, hnc⟩ := deadAt_deadPt g st P hE
  set E' := upd2 E (dc g st P E 0) (dc g st P E 1) w
  have hnot : ∀ c, c < 2 → dc g st P E c ∉ (cipherLog (jOf g P E)).map Sigma.fst := by
    intro c hc h
    obtain ⟨q, hq, hqe⟩ := List.mem_map.1 h
    refine hnc ⟨q, hq, ?_⟩
    interval_cases c
    · exact Or.inl hqe
    · exact Or.inr hqe
  have hJ : ∀ t ∈ (jOf g P E).map Sigma.fst, join g E' t = join g E t := by
    intro t ht
    cases t with
    | inl d => rw [join_inl, join_inl]
    | inr x =>
      have hx := mem_cipherLog.2 ht
      rw [join_inr, join_inr]
      exact upd2_apply_of_ne E (fun h => hnot 0 (by norm_num) (by rw [← h]; exact hx))
        (fun h => hnot 1 (by norm_num) (by rw [← h]; exact hx)) w
  obtain ⟨hP, hL⟩ := tableQueryLog_congr P (join g E) (join g E') hJ
  have hπ : πOf g P E' = πOf g P E := congrArg Prod.fst hP
  have hJ' : jOf g P E' = jOf g P E := hL
  have hiv : ivE g st P E' = ivE g st P E := by simp only [ivE, hπ]
  have hrt : rtOf g st P E' = rtOf g st P E := by
    unfold rtOf
    rw [hiv, hπ]
    refine recTree_ic_congr_cells fun k n hn c hc => ?_
    refine cipher_upd2_of_ne E _ _ w k ?_ ?_
    · rw [dc_snd]
      exact (lp_ne_gp _ 0 c hi hn).symm
    · rw [dc_snd]
      exact (lp_ne_gp _ 1 c hi hn).symm
  have hdead : DeadAt g st P E' = DeadAt g st P E := by
    funext p
    simp only [DeadAt, hπ, hJ', hiv, hrt]
  have hpt : deadPt g st P E' = deadPt g st P E := by simp only [deadPt, hdead]
  have hkey : deadKey g st P E' = deadKey g st P E := by simp only [deadKey, hrt, hpt]
  refine ⟨?_, ?_, ?_⟩
  · simp only [dc, hkey, hiv, hpt]
  · simp only [dc, hkey, hiv, hpt]
  · simp only [deadTargets, hJ', hpt]

/-- **The dead leaf's two cell values are a target**: the leaf hash of its tree is one of `P`'s
`H₁` inputs, and its block `j` is the leaf's commitment `E_{s'}(x₀) ‖ E_{s'}(x₁)`. -/
theorem deadQueried_mem {E : CTable} (hE : DeadQueried g st P E) :
    (E (dc g st P E 0), E (dc g st P E 1)) ∈ deadTargets g st P E := by
  obtain ⟨⟨leaves, hr, hall⟩, hex⟩ := hE
  obtain ⟨hi, hj, hjd, -⟩ := deadAt_deadPt g st P hex
  set i := (deadPt g st P E).1
  set j := (deadPt g st P E).2
  have hlen : i < (BAVC.leafHashInputs leaves.coms).length := by
    rw [length_leafHashInputs]; exact hi
  set w := (BAVC.leafHashInputs leaves.coms)[i]
  have hw : ((.h1, w) : Dom) ∈ hashLog (jOf g P E) := hall w (List.getElem_mem hlen)
  have hblk : w.extract (32 * j) (32 * j + 32) =
      ba (E (dc g st P E 0)) ++ ba (E (dc g st P E 1)) := by
    let _ : HasPrg := icPrg E.cipher
    rw [extract_leafHashInput (reconstruct_coms_size hr) hi hj, comAt_reconstruct hr hi hj hjd]
    have hk := @leafKey_reconstruct (icPrg E.cipher) _ _ _ leaves hr i j hi hj hjd
    have hks := leafKey_size hr hi hj hjd
    rw [← ba_blk_of_size hks, leafCom_ic]
    simp only [dc, deadKey, CTable.cipher, rtOf, hk]
    rfl
  refine List.mem_toFinset.2 (List.mem_map.2 ⟨w, mem_kindIns hw, ?_⟩)
  rw [hblk, split32_ba]

/-- **A dead leaf whose leaf hash `P` queried**, for a fixed hash table: probability at most
`q₁·2⁻²⁵⁶` over the cipher table (two fresh cells guessed against `P`'s at most `q₁` `H₁`
inputs). -/
theorem prEvent_deadQueried_le (q : Kind → ℕ) (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable}[DeadQueried g st P E] ≤ q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  refine prEvent_two_cells_le _ (fun E => dc g st P E 0) (fun E => dc g st P E 1)
    (deadTargets g st P) (q .h1) (fun E _ h => ?_) (fun E hE w => deadQueried_inv g st P hE.2 w)
    (fun E _ => ?_) (fun E hE => deadQueried_mem g st P hE)
  · have h2 := congrArg Prod.snd h
    rw [dc_snd, dc_snd] at h2
    exact lp_ne (ivE g st P E) _ h2
  · refine (List.toFinset_card_le _).trans ?_
    rw [List.length_map]
    exact length_kindIns_hashLog_le P hq (join g E) .h1

end Dead

/-! ## `ε_open` -/

section Open

variable {β : Type}

lemma gameIC_fst (T : CrtTables) (st : Statement) (P : OracleComp specIC (ByteArray × β)) (g : Table)
    (E : CTable) : (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)).1 = πOf g P E := by
  simp only [gameIC, evalWithAnswerFn_game, evalWithAnswerFn_proverIC, πOf]

lemma gameIC_aux (T : CrtTables) (st : Statement) (P : OracleComp specIC (ByteArray × β)) (g : Table)
    (E : CTable) : (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)).2.1.aux.2 = jOf g P E := by
  simp only [gameIC, evalWithAnswerFn_game, evalWithAnswerFn_proverIC, jOf]

lemma gameIC_tr (T : CrtTables) (st : Statement) (P : OracleComp specIC (ByteArray × β)) (g : Table)
    (E : CTable) : (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)).2.2 =
      @verify (icPrg E.cipher) (Hashes.ofTable g) T st (πOf g P E) := by
  simp only [gameIC, evalWithAnswerFn_game, evalWithAnswerFn_proverIC, πOf]

/-- **An opened dead leaf, all of whose leaf hashes `P` queried, is `DeadQueried`** (at a hash
table `g`). -/
theorem deadQueried_of_deadOpen (T : CrtTables) (st : Statement)
    (P : OracleComp specIC (ByteArray × β)) (g : Table) (E : CTable)
    (hD : DeadOpenOut st E (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)))
    (hL : ¬@LeafUnqueried (icPrg E.cipher) _ st
      (hashLog (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)).2.1.aux.2)
      (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E))) :
    DeadQueried g st P E := by
  let _ : HasPrg := icPrg E.cipher
  obtain ⟨hacc, leaves, hr, i, hi, j, hj, hjd, hnc⟩ := hD
  have hL' : ∀ w ∈ BAVC.leafHashInputs leaves.coms, ((.h1, w) : Dom) ∈
      hashLog (evalWithAnswerFn (QueryImpl.ofFn g) (gameIC T st P E)).2.1.aux.2 := by
    intro w hw
    by_contra hwq
    exact hL ⟨leaves, hr, w, hw, hwq⟩
  rw [gameIC_aux] at hL' hnc
  rw [gameIC_fst] at hr hjd
  rw [gameIC_tr] at hacc hr hnc
  obtain ⟨-, leaves', hr', -⟩ := (accept_iff _ T st (πOf g P E)).1 hacc
  have hiv : (@verify (icPrg E.cipher) (Hashes.ofTable g) T st (πOf g P E)).iv = ivE g st P E :=
    (verify_iv_chal1 _ T st _ hacc hr').1
  rw [hiv] at hr hnc
  have hr'' : @BAVC.reconstruct (icPrg E.cipher) (ivE g st P E)
      (Proof.opening ⟨st.params, πOf g P E⟩) (Proof.delta ⟨st.params, πOf g P E⟩) = some leaves := hr
  have hdead : DeadAt g st P E (i, j) := by
    refine ⟨hi, hj, hjd, ?_⟩
    have hk := @leafKey_reconstruct (icPrg E.cipher) _ _ _ leaves hr'' i j hi hj hjd
    show ¬HasCell (cipherLog (jOf g P E)) (blk 16 (rtOf g st P E)[BAVC.treePos i j]!)
      (lp (ivE g st P E) i 0) (lp (ivE g st P E) i 1)
    rw [rtOf, ← hk]
    exact hnc
  exact ⟨⟨leaves, hr'', hL'⟩, ⟨(i, j), hdead⟩⟩

/-- Joint-experiment monotonicity. -/
lemma prEvent_joint_mono {X : Type} (m : CTable → ProbComp X) (p p' : CTable → X → Prop)
    (h : ∀ E r, p E r → p' E r) :
    Pr{let E ← $ᵗ CTable; let r ← m E}[p E r] ≤ Pr{let E ← $ᵗ CTable; let r ← m E}[p' E r] := by
  let : MeasurableSpace CTable := ⊤
  rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete]
  exact lintegral_mono fun E => prEvent_mono _ _ _ (h E)

/-- Joint-experiment union bound. -/
lemma prEvent_joint_or_le {X : Type} (m : CTable → ProbComp X) (p p' : CTable → X → Prop) :
    Pr{let E ← $ᵗ CTable; let r ← m E}[p E r ∨ p' E r] ≤
      Pr{let E ← $ᵗ CTable; let r ← m E}[p E r] + Pr{let E ← $ᵗ CTable; let r ← m E}[p' E r] := by
  let : MeasurableSpace CTable := ⊤
  rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete, prEvent_bind_of_discrete]
  calc ∫⁻ E, Pr{let r ← m E}[p E r ∨ p' E r] ∂𝒟[$ᵗ CTable]
      ≤ ∫⁻ E, (Pr{let r ← m E}[p E r] + Pr{let r ← m E}[p' E r]) ∂𝒟[$ᵗ CTable] :=
        lintegral_mono fun E => prEvent_or_le _ _ _
    _ = _ := lintegral_add_left measurable_from_top _

lemma prEvent_joint_false {X : Type} (m : CTable → ProbComp X) :
    Pr{let E ← $ᵗ CTable; let r ← m E}[(fun _ _ => False : CTable → X → Prop) E r] = 0 := by
  let : MeasurableSpace CTable := ⊤
  rw [prEvent_bind_of_discrete]
  simp

/-- **`ε_open`, explicitly**: in the joint experiment, an accepted proof opens a dead leaf with
probability at most

    (q₁+18)·(17q₁+q₂₁)·2⁻²⁵⁶ + (q₂₁+1)·q₂₂·2⁻¹⁰⁸⁸ + (q₂₂+1)·q₂₃·2⁻⁴⁴⁸ + 2⁻¹²⁸ + q₁·2⁻²⁵⁶

(`openHashEps q + q₁·2⁻²⁵⁶`), for a prover with `q k` hash queries of each kind `k`. -/
theorem prEvent_joint_deadOpen_le (T : CrtTables) (st : Statement)
    (P : OracleComp specIC (ByteArray × β)) (q : Kind → ℕ) (hq : IsKindQueryBoundIC P q) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle (gameIC T st P E)).run' ∅}[
        DeadOpenOut st E r] ≤ openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  let m : CTable → ProbComp (Out (β × QueryLog specIC)) := fun E =>
    (simulateQ randomOracle (gameIC T st P E)).run' ∅
  let A : CTable → Out (β × QueryLog specIC) → Prop := fun E r =>
    r.2.2.accept = true ∧ @LeafUnqueried (icPrg E.cipher) _ st (hashLog r.2.1.aux.2) r
  have h1 : Pr{let E ← $ᵗ CTable; let r ← m E}[A E r] ≤ openHashEps q := by
    have h := prEvent_avg_le_add m A (fun _ _ => False) (openHashEps q) fun E =>
      (prEvent_leafUnqueried_ic_le T st P q hq E).trans le_self_add
    rwa [prEvent_joint_false, add_zero] at h
  have h2 : Pr{let E ← $ᵗ CTable; let r ← m E}[DeadOpenOut st E r ∧ ¬A E r] ≤
      q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
    have h := prEvent_joint_le_add (gameIC T st P) (fun E r => DeadOpenOut st E r ∧ ¬A E r)
      (fun _ _ => False) (q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹) fun g =>
        ((prEvent_mono _ _ _ fun E h => deadQueried_of_deadOpen T st P g E h.1
          fun hL => h.2 ⟨h.1.1, hL⟩).trans (prEvent_deadQueried_le g st P q hq)).trans le_self_add
    rwa [prEvent_joint_false, add_zero] at h
  calc Pr{let E ← $ᵗ CTable; let r ← m E}[DeadOpenOut st E r]
      ≤ Pr{let E ← $ᵗ CTable; let r ← m E}[A E r ∨ (DeadOpenOut st E r ∧ ¬A E r)] :=
        prEvent_joint_mono m _ _ fun E r h => (em (A E r)).elim Or.inl fun hA => Or.inr ⟨h, hA⟩
    _ ≤ _ := (prEvent_joint_or_le m _ _).trans (add_le_add h1 h2)

/-- **Moussaka issuance in the random-oracle and ideal-cipher model, binding explicit**:
`moussakaIssue_accept_le_ic` with `ε_open` replaced by its bound `prEvent_joint_deadOpen_le`,

    Pr[accept ∧ ¬Extracted] ≤ (q₂₁+1)·2⁻¹⁵⁰ + (q₂₂+1)·ε_QS(4008) + (q₂₃+1)·9·2⁻¹²⁸
      + (2·q_E²·2⁻²⁵⁶ + openHashEps q + q₁·2⁻²⁵⁶) + ε_dead + ε_chain + Σ_k q'_k·εh_k,

`openHashEps q = (q₁+18)·(17q₁+q₂₁)·2⁻²⁵⁶ + (q₂₁+1)·q₂₂·2⁻¹⁰⁸⁸ + (q₂₂+1)·q₂₃·2⁻⁴⁴⁸ +
2⁻¹²⁸`. What remains assumed: `hsame` and `hL2` with their failure events and hits
(`ROM/CipherChain.lean` discharges them). -/
theorem moussakaIssue_accept_le_ic' (t ctxIss : ByteArray) (labelRows : Bool)
    (preOf midOf : CTable → ByteArray → Table → Chain)
    (accOf : CTable → ByteArray → Table → Prob.Bytes 16 → Prop)
    (hC : ∀ E, (ChainData.ofSys (st := moussakaIssue t ctxIss labelRows) (preOf E) (midOf E)
      (moussakaIssueSys t ctxIss) (accOf E)).Committed)
    (P : OracleComp specIC (ByteArray × β)) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) (q : Kind → ℕ)
    (hq : IsKindQueryBoundIC P q)
    (chainFail deadFail : CTable → Out (β × QueryLog specIC) → Prop) {εd εs : ℝ≥0∞}
    (hdead : Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (moussakaIssue t ctxIss labelRows) P E)).run' ∅}[deadFail E r] ≤ εd)
    (hchain : Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (moussakaIssue t ctxIss labelRows) P E)).run' ∅}[chainFail E r] ≤ εs)
    (deadOf : CTable → Table → Fin BAVC.tau → Finset ℕ) (hit : CTable → Dom → Table → Prop)
    (εh : Kind → ℝ≥0∞) (hεh : ∀ k ∉ hitKinds, εh k = 0)
    (hhit : ∀ E t g, Pr{let u ← $ᵗ (Ans t)}[hit E t (Function.update g t u)] ≤ εh t.1)
    (hsame : ∀ E : CTable, @SameChainHyp (icPrg E.cipher) _ CrtGen.tables
      (moussakaIssue t ctxIss labelRows) (proverIC (moussakaIssue t ctxIss labelRows) E P)
      (preOf E) (midOf E) (accOf E) (deadOf E) (hit E) (chainFail E))
    (hL2 : ∀ E : CTable, @DeadHiddenHyp (icPrg E.cipher) _ CrtGen.tables
      (moussakaIssue t ctxIss labelRows) (proverIC (moussakaIssue t ctxIss labelRows) E P)
      (deadOf E) (hit E) (chainFail E) (deadFail E)) :
    Pr{let E ← $ᵗ CTable; let r ← (simulateQ randomOracle
      (gameIC CrtGen.tables (moussakaIssue t ctxIss labelRows) P E)).run' ∅}[
        r.2.2.accept = true ∧ ¬@Extracted (icPrg E.cipher) _ (moussakaIssue t ctxIss labelRows)
          (fun _ => moussakaIssueWit (fun k => fnOf t k.val) (fnOf ctxIss)) r] ≤
      (q .h21 + 1) * (2 ^ 150 : ℝ≥0∞)⁻¹ +
        (q .h22 + 1) * ENNReal.ofReal (Seed.epsQS (2 ^ 128) (2 ^ 64) 4008) +
        (q .h23 + 1) * ((9 : ℝ≥0∞) / 2 ^ 128) +
        (2 * qE ^ 2 * (2 ^ 256)⁻¹ + (openHashEps q + q .h1 * (2 ^ 256 : ℝ≥0∞)⁻¹)) + εd + εs +
        hitSum (q + verifierQueries) εh :=
  moussakaIssue_accept_le_ic t ctxIss labelRows preOf midOf accOf hC P qE hqE q hq chainFail
    deadFail (prEvent_joint_deadOpen_le CrtGen.tables _ P q hq) hdead hchain deadOf hit εh hεh hhit
    hsame hL2

end Open

end VoleMole.ROM.IC



