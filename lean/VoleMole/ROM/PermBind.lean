import VoleMole.ROM.PermCount
import VoleMole.ROM.CipherSame

/-!
# Prefix-local cipher events and the collision bound, in the permutation model

* **`prEvent_perm_prefix_le`** (the generic bound for an event charged at one record): the
  `n`-th cipher record of the normalized prover's log (`jP`) is under a key `κ`, and some target
  `j` of the log *before* it (`TT pre κ π`, which may read the table at keys other than `κ`) names
  two inputs of `κ` that are not recorded before it and that `π_κ` maps to the target's two values.
  The key, the protected inputs (`keyIns κ pre`, at most `n`) and the targets only depend on the
  records of the prefix (`normP_prefix`), so `prEvent_perm_two_le` gives
  `≤ K / ((2¹²⁸ − n)(2¹²⁸ − n − 1))`. The `n`-th record may come from a forward query `(κ, z)` or
  from an inverse query `(κ, y)` (whose input is the random `π_κ⁻¹(y)`): only its key is used.
* **The collision event** of `ROM/CipherBind.lean` (`collBad`, the C2-type double collision),
  unchanged, on the normalized prover's records: **`prEvent_perm_coll_le`**,
  `Pr_π[fresh collBad] ≤ 2·q_E²·p²` with `p = 1/(2¹²⁸ − q_E)` (the PRF view's `2·q_E²·2⁻²⁵⁶` with
  `2⁻¹²⁸` replaced by `p`; the targets of a record are the other keys' records at a neighbour,
  `collT`, four per earlier record, so the adjacency `w ↦ w ⊞ e₀`, `w ⊟ e₀` must be symmetric:
  `prv_nxt`, `nxt_prv`).
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim VoleMole.ROM

/-! ## The two neighbours are inverse to each other -/

lemma bytes_getLE32 (b : ByteArray) (o : ℕ) :
    (AES.getLE32 b o).toUInt8 = b.get! o ∧ (AES.getLE32 b o >>> 8).toUInt8 = b.get! (o + 1) ∧
      (AES.getLE32 b o >>> 16).toUInt8 = b.get! (o + 2) ∧
      (AES.getLE32 b o >>> 24).toUInt8 = b.get! (o + 3) := by
  have h0 := (b.get! o).toNat_lt
  have h1 := (b.get! (o + 1)).toNat_lt
  have h2 := (b.get! (o + 2)).toNat_lt
  have h3 := (b.get! (o + 3)).toNat_lt
  have e : (AES.getLE32 b o).toNat = (b.get! o).toNat + 2 ^ 8 * (b.get! (o + 1)).toNat +
      2 ^ 16 * (b.get! (o + 2)).toNat + 2 ^ 24 * (b.get! (o + 3)).toNat := toNat_le32 _ _ _ _
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.1 <;>
    simp only [UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, UInt32.reduceToNat,
      Nat.shiftRight_eq_div_pow, Nat.reduceMod, Nat.reducePow, e] <;> omega

lemma get!_ctrBlock_zero (b : ByteArray) {t : ℕ} (ht : t < 16) :
    (AES.ctrBlock b 0 0).get! t = b.get! t := by
  obtain ⟨a0, a1, a2, a3⟩ := bytes_getLE32 b 0
  obtain ⟨b0, b1, b2, b3⟩ := bytes_getLE32 b 4
  obtain ⟨c0, c1, c2, c3⟩ := bytes_getLE32 b 8
  obtain ⟨d0, d1, d2, d3⟩ := bytes_getLE32 b 12
  simp only [AES.ctrBlock, add_zero]
  interval_cases t <;> simp [get!_pushLE32, size_pushLE32, a0, a1, a2, a3, b0, b1, b2, b3, c0,
    c1, c2, c3, d0, d1, d2, d3]

lemma blk_ctrBlock_zero (w : Blk) : blk 16 (AES.ctrBlock (ba w) 0 0) = w := by
  funext t
  rw [get_blk, get!_ctrBlock_zero _ t.isLt, get!_ba _ t.isLt]

lemma prv_nxt (w : Blk) : prv (nxt w) = w := by
  simp only [prv, nxt, ba_blk_of_size (ctrBlock_size _ _ _), ctrBlock_ctrBlock]
  rw [show (1 : UInt32) + (0 - 1) = 0 by decide, show (0 : UInt32) + 0 = 0 by decide]
  exact blk_ctrBlock_zero w

lemma nxt_prv (w : Blk) : nxt (prv w) = w := by
  simp only [prv, nxt, ba_blk_of_size (ctrBlock_size _ _ _), ctrBlock_ctrBlock]
  rw [show (0 - 1 : UInt32) + 1 = 0 by decide, show (0 : UInt32) + 0 = 0 by decide]
  exact blk_ctrBlock_zero w

/-- **The neighbour relation is symmetric.** -/
lemma mem_adj_symm {w u : Blk} (h : u ∈ adj w) : w ∈ adj u := by
  rcases mem_adj.1 h with rfl | rfl
  · exact mem_adj.2 (Or.inr (prv_nxt w).symm)
  · exact mem_adj.2 (Or.inl (nxt_prv w).symm)

/-! ## Records of a prefix -/

/-- The inputs recorded under the key `κ` in a joint-log prefix. -/
def keyIns (κ : Blk) (pre : QueryLog specIC) : Finset Blk :=
  ((cipherLog pre).filterMap fun e => if e.1.1 = κ then some e.1.2 else none).toFinset

lemma mem_keyIns {κ z : Blk} {pre : QueryLog specIC} :
    z ∈ keyIns κ pre ↔ (.inr (κ, z) : DomIC) ∈ pre.map Sigma.fst := by
  rw [← mem_cipherLog]
  unfold keyIns
  rw [List.mem_toFinset, List.mem_filterMap, List.mem_map]
  constructor
  · rintro ⟨e, he, hez⟩
    split_ifs at hez with hk
    · cases hez
      exact ⟨e, he, Prod.ext hk rfl⟩
  · rintro ⟨e, he, hez⟩
    exact ⟨e, he, by rw [hez]; simp⟩

lemma card_keyIns_le (κ : Blk) (pre : QueryLog specIC) :
    #(keyIns κ pre) ≤ (cipherLog pre).length :=
  (List.toFinset_card_le _).trans (List.length_filterMap_le _ _)

lemma length_cipherLog_beforeCipher : ∀ (n : ℕ) (L : QueryLog specIC),
    (cipherLog (beforeCipher n L)).length ≤ n
  | _, [] => by simp [beforeCipher]
  | n, ⟨.inl d, u⟩ :: L => by
    show (cipherLog (beforeCipher n L)).length ≤ n
    exact length_cipherLog_beforeCipher n L
  | 0, ⟨.inr _, _⟩ :: _ => by simp [beforeCipher]
  | n + 1, ⟨.inr x, u⟩ :: L => by
    show (⟨x, u⟩ :: cipherLog (beforeCipher n L)).length ≤ n + 1
    have := length_cipherLog_beforeCipher n L
    rw [List.length_cons]
    omega

lemma exists_of_kthCell : ∀ {n : ℕ} {L : QueryLog specIC} {c : Cell}, kthCell n L = some c →
    ∃ pre u post, L = pre ++ (⟨.inr c, u⟩ : (t : DomIC) × AnsIC t) :: post ∧
      (cipherLog pre).length = n
  | _, [], _, h => by simp [kthCell] at h
  | n, ⟨.inl d, u⟩ :: L, c, h => by
    simp only [kthCell] at h
    obtain ⟨pre, v, post, rfl, hn⟩ := exists_of_kthCell h
    exact ⟨⟨.inl d, u⟩ :: pre, v, post, rfl, hn⟩
  | 0, ⟨.inr x, u⟩ :: L, c, h => by
    simp only [kthCell, Option.some.injEq] at h
    subst h
    exact ⟨[], u, L, rfl, rfl⟩
  | n + 1, ⟨.inr x, u⟩ :: L, c, h => by
    simp only [kthCell] at h
    obtain ⟨pre, v, post, rfl, hn⟩ := exists_of_kthCell h
    refine ⟨⟨.inr x, u⟩ :: pre, v, post, rfl, ?_⟩
    show (⟨x, u⟩ :: cipherLog pre).length = n + 1
    rw [List.length_cons, hn]

variable {α : Type} (p : Params)

/-- A record of the normalized prover's log is answered by the forward table. -/
lemma answer_of_mem_jP {h : Table} {σ : PTable} {P : OracleComp specP α} {c : Cell} {v : Blk}
    (hm : (⟨.inr c, v⟩ : (t : DomIC) × AnsIC t) ∈ jP p h σ P) : σ c.1 c.2 = v := by
  have := tableQueryLog_answer (normP p σ P) (join h σ.fwd) _ hm
  exact (eq_of_heq (Sigma.mk.inj this).2).symm

/-! ## The bound for an event charged at one record -/

/-- **An event charged at the `n`-th record** (see the module docstring): probability at most
`K / ((2¹²⁸ − n)(2¹²⁸ − n − 1))`. -/
theorem prEvent_perm_prefix_le {J : Type} [Fintype J] (h : Table) (P : OracleComp specP α)
    (n : ℕ) (TT : QueryLog specIC → Blk → PTable → Finset J)
    (hTT : ∀ pre κ σ σ', (∀ κ', κ' ≠ κ → σ' κ' = σ κ') → TT pre κ σ' = TT pre κ σ)
    (z₁ z₂ y₁ y₂ : J → Blk) (hz : ∀ pre κ σ j, j ∈ TT pre κ σ → z₁ j ≠ z₂ j) (K : ℕ)
    (hK : ∀ σ κ, #(TT (beforeCipher n (jP p h σ P)) κ σ) ≤ K) :
    Pr{let π ← $ᵗ PTable}[∃ pre e post κ w, jP p h π P = pre ++ e :: post ∧
        (cipherLog pre).length = n ∧ e.1 = .inr (κ, w) ∧ ∃ j ∈ TT pre κ π,
        (.inr (κ, z₁ j) : DomIC) ∉ pre.map Sigma.fst ∧
        (.inr (κ, z₂ j) : DomIC) ∉ pre.map Sigma.fst ∧ π κ (z₁ j) = y₁ j ∧ π κ (z₂ j) = y₂ j] ≤
      K * ((((2 ^ 128 - n) * (2 ^ 128 - n - 1) : ℕ) : ℝ≥0∞))⁻¹ := by
  let kk : PTable → Blk := fun σ => ((kthCell n (jP p h σ P)).getD default).1
  let XX : PTable → Finset Blk := fun σ => keyIns (kk σ) (beforeCipher n (jP p h σ P))
  let TTT : PTable → Finset J := fun σ => TT (beforeCipher n (jP p h σ P)) (kk σ) σ
  let ev : J → PTable → Prop := fun j σ => (kthCell n (jP p h σ P)).isSome ∧ j ∈ TTT σ ∧
    z₁ j ≠ z₂ j ∧ z₁ j ∉ XX σ ∧ z₂ j ∉ XX σ ∧ σ (kk σ) (z₁ j) = y₁ j ∧ σ (kk σ) (z₂ j) = y₂ j
  have hdec : ∀ σ pre (e : (t : DomIC) × AnsIC t) post κ w, jP p h σ P = pre ++ e :: post →
      (cipherLog pre).length = n → e.1 = .inr (κ, w) →
      kk σ = κ ∧ beforeCipher n (jP p h σ P) = pre ∧ kthCell n (jP p h σ P) = some (κ, w) := by
    intro σ pre e post κ w hJ hn he
    have hs := beforeCipher_kthCell (pre := pre) (post := post) he
    rw [hn, ← hJ] at hs
    exact ⟨by simp only [kk, hs.2, Option.getD_some], hs.1, hs.2⟩
  refine (prEvent_mono _ _ (fun π => ∃ j, ev j π) ?_).trans
    (prEvent_perm_two_le ev kk XX TTT z₁ z₂ y₁ y₂ K n ?_ ?_ ?_ ?_)
  · rintro π ⟨pre, e, post, κ, w, hJ, hn, he, j, hj, h1, h2, h3, h4⟩
    obtain ⟨hk, hb, hc⟩ := hdec π pre e post κ w hJ hn he
    refine ⟨j, by rw [hc]; rfl, ?_, hz _ _ _ _ hj, ?_, ?_, ?_, ?_⟩
    · show j ∈ TT (beforeCipher n (jP p h π P)) (kk π) π
      rw [hb, hk]; exact hj
    · show z₁ j ∉ keyIns (kk π) (beforeCipher n (jP p h π P))
      rw [hb, hk, mem_keyIns]; exact h1
    · show z₂ j ∉ keyIns (kk π) (beforeCipher n (jP p h π P))
      rw [hb, hk, mem_keyIns]; exact h2
    · rw [hk]; exact h3
    · rw [hk]; exact h4
  · intro j σ hj
    exact hj.2
  · rintro j σ ⟨hs, -⟩ π hoff hX
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hs
    obtain ⟨pre, u, post, hJ, hn⟩ := exists_of_kthCell hc
    obtain ⟨hk, hb, -⟩ := hdec σ pre _ post c.1 c.2 hJ hn rfl
    obtain ⟨w', v', post', hJ'⟩ := normP_prefix p P h σ π pre post _ c.1 c.2 hJ rfl
      (fun c' v hc' => by
        have hmem : (⟨.inr c', v⟩ : (t : DomIC) × AnsIC t) ∈ jP p h σ P := by
          rw [hJ]; exact List.mem_append_left _ hc'
        rw [← answer_of_mem_jP p hmem]
        by_cases hkc : c'.1 = kk σ
        · have hx : c'.2 ∈ XX σ := by
            show c'.2 ∈ keyIns (kk σ) (beforeCipher n (jP p h σ P))
            rw [hb, mem_keyIns, ← hkc]
            exact List.mem_map.2 ⟨_, hc', rfl⟩
          have := hX c'.2 hx
          rw [← hkc] at this
          exact this
        · rw [hoff c'.1 hkc])
    obtain ⟨hk', hb', -⟩ := hdec π pre _ post' c.1 w' hJ' hn rfl
    refine ⟨hk'.trans hk.symm, ?_⟩
    show TT (beforeCipher n (jP p h π P)) (kk π) π = TT (beforeCipher n (jP p h σ P)) (kk σ) σ
    rw [hb', hk', hb, hk]
    exact hTT pre c.1 σ π fun κ' hκ' => hoff κ' (hk ▸ hκ')
  · intro σ
    exact (card_keyIns_le _ _).trans (length_cipherLog_beforeCipher _ _)
  · intro σ
    exact hK σ (kk σ)

/-! ## The collision bound -/

/-- **The collision targets of a prefix** for a record under `κ`: for every earlier record
`(κ', u)` of another key, the two neighbour pairs through `u`, in both orders, with `κ'`'s
values there. -/
def collT (l : QueryLog cspec) (κ : Blk) (σ : PTable) : Finset (Blk × Blk × Blk × Blk) :=
  (l.flatMap fun e => if e.1.1 = κ then [] else
    [(e.1.2, nxt e.1.2), (e.1.2, prv e.1.2), (nxt e.1.2, e.1.2), (prv e.1.2, e.1.2)].map
      fun ww => (ww.1, ww.2, σ e.1.1 ww.1, σ e.1.1 ww.2)).toFinset

lemma collT_congr (l : QueryLog cspec) (κ : Blk) (σ σ' : PTable)
    (hσ : ∀ κ', κ' ≠ κ → σ' κ' = σ κ') : collT l κ σ' = collT l κ σ := by
  unfold collT
  congr 1
  induction l with
  | nil => rfl
  | cons e l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, ih]
    split_ifs with hk
    · rfl
    · rw [hσ _ hk]

lemma card_collT_le (l : QueryLog cspec) (κ : Blk) (σ : PTable) :
    #(collT l κ σ) ≤ 4 * l.length := by
  unfold collT
  refine (List.toFinset_card_le _).trans ?_
  induction l with
  | nil => simp
  | cons e l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    split_ifs
    · simp only [List.length_nil, zero_add]; omega
    · simp only [List.length_map, List.length_cons, List.length_nil]; omega

lemma mem_collT_ne {l : QueryLog cspec} {κ : Blk} {σ : PTable} {j : Blk × Blk × Blk × Blk}
    (hj : j ∈ collT l κ σ) : j.1 ≠ j.2.1 := by
  unfold collT at hj
  obtain ⟨e, -, he⟩ := List.mem_flatMap.1 (List.mem_toFinset.1 hj)
  split_ifs at he
  · simp at he
  · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact (nxt_ne _).symm
    · exact (prv_ne _).symm
    · exact nxt_ne _
    · exact prv_ne _

lemma pE_mono {m n : ℕ} (h : m ≤ n) : pE m ≤ pE n := by
  unfold pE
  exact ENNReal.inv_le_inv.2 (Nat.cast_le.2 (by omega))

lemma sum_range_four_mul_le (q : ℕ) : ∑ n ∈ range q, 4 * n ≤ 2 * q ^ 2 := by
  rw [← mul_sum]
  have := Finset.sum_range_id_mul_two q
  have h2 : q * (q - 1) ≤ q ^ 2 := by rw [sq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  omega

/-- **The collision bound in the permutation model**: a fresh `collBad` record of the normalized
prover (at most `q_E` cipher queries, forward or inverse) has probability at most `2·q_E²·p²`,
`p = 1/(2¹²⁸ − q_E)`, at every hash table. -/
theorem prEvent_perm_coll_le (h : Table) (P : OracleComp specP α) (qE : ℕ)
    (hqE : IsQueryBoundP P (fun t => t.isRight = true) qE) :
    Pr{let π ← $ᵗ PTable}[freshBadC (runH h (normP p π P)) ∅ π.fwd collBad] ≤
      2 * qE ^ 2 * pE qE ^ 2 := by
  classical
  let TT : QueryLog specIC → Blk → PTable → Finset (Blk × Blk × Blk × Blk) :=
    fun pre κ σ => collT (cipherLog pre) κ σ
  let Ev : ℕ → PTable → Prop := fun n π => ∃ pre e post κ w, jP p h π P = pre ++ e :: post ∧
    (cipherLog pre).length = n ∧ e.1 = .inr (κ, w) ∧ ∃ j ∈ TT pre κ π,
    (.inr (κ, j.1) : DomIC) ∉ pre.map Sigma.fst ∧
    (.inr (κ, j.2.1) : DomIC) ∉ pre.map Sigma.fst ∧ π κ j.1 = j.2.2.1 ∧ π κ j.2.1 = j.2.2.2
  have hstep : ∀ n, Pr{let π ← $ᵗ PTable}[Ev n π] ≤ ((4 * n : ℕ) : ℝ≥0∞) * pE qE ^ 2 ∨
      qE ≤ n := by
    intro n
    by_cases hn : n < qE
    · left
      refine (prEvent_perm_prefix_le p h P n TT (fun pre κ σ σ' hσ => collT_congr _ κ σ σ' hσ)
        (fun j => j.1) (fun j => j.2.1) (fun j => j.2.2.1) (fun j => j.2.2.2)
        (fun pre κ σ j hj => mem_collT_ne hj) (4 * n) (fun σ κ => (card_collT_le _ _ _).trans
          (Nat.mul_le_mul_left _ (length_cipherLog_beforeCipher _ _)))).trans ?_
      gcongr
      exact (inv_two_le_pE n).trans (pow_le_pow_left₀ (zero_le) (pE_mono (by omega)) 2)
    · exact Or.inr (by omega)
  have hcover : ∀ π : PTable, freshBadC (runH h (normP p π P)) ∅ π.fwd collBad →
      ∃ n ∈ range qE, Ev n π := by
    intro π hfb
    rw [freshBadC_empty_iff] at hfb
    obtain ⟨cpre, q, cpost, hlog, hfresh, hbad⟩ := hfb
    rw [← cipherLog_tableQueryLog] at hlog
    obtain ⟨R₁, R₂, hJ, hR⟩ := exists_split_cipherLog hlog
    have hlen : cpre.length < qE := by
      have := length_cipherLog_le _ (isQueryBoundP_right_normP p π hqE) (join h π.fwd)
      rw [hlog, List.length_append, List.length_cons] at this
      omega
    obtain ⟨⟨k, w⟩, v⟩ := q
    obtain ⟨w', hw', κ, hκ, hn, hs, h1, h2⟩ := hbad
    simp only at hw' hκ hn hs h1 h2 hfresh
    have hnone : ∀ d, cacheOfLog (∅ : cspec.QueryCache) cpre d = none → ∀ e ∈ cpre, e.1 ≠ d :=
      fun d hd => ((cacheOfLog_eq_none _ _ _).1 hd).2
    have hsome : ∀ d, (cacheOfLog (∅ : cspec.QueryCache) cpre d).isSome → ∃ e ∈ cpre, e.1 = d := by
      intro d hd
      by_contra hc
      rw [Option.isSome_iff_ne_none, ne_eq, cacheOfLog_eq_none] at hd
      exact hd ⟨rfl, fun e he he1 => hc ⟨e, he, he1⟩⟩
    refine ⟨cpre.length, mem_range.2 hlen, R₁, _, R₂, k, w, hJ, by rw [hR], rfl,
      (w, w', π κ w, π κ w'), ?_, ?_, ?_, ?_, ?_⟩
    · show (w, w', π κ w, π κ w') ∈ collT (cipherLog R₁) k π
      rw [hR]
      unfold collT
      rw [List.mem_toFinset, List.mem_flatMap]
      rcases hs with hs | hs
      · obtain ⟨e, he, he1⟩ := hsome _ hs
        refine ⟨e, he, ?_⟩
        rw [he1]
        simp only [hκ, ↓reduceIte]
        rcases mem_adj.1 hw' with rfl | rfl <;> simp
      · obtain ⟨e, he, he1⟩ := hsome _ hs
        refine ⟨e, he, ?_⟩
        rw [he1]
        simp only [hκ, ↓reduceIte]
        rcases mem_adj.1 (mem_adj_symm hw') with h' | h' <;> rw [h'] <;> simp
    · rw [← mem_cipherLog, hR]
      intro hm
      obtain ⟨e, he, he1⟩ := List.mem_map.1 hm
      exact hfresh e he he1
    · rw [← mem_cipherLog, hR]
      intro hm
      obtain ⟨e, he, he1⟩ := List.mem_map.1 hm
      exact hnone _ hn e he he1
    · exact h1.symm
    · exact h2.symm
  calc Pr{let π ← $ᵗ PTable}[freshBadC (runH h (normP p π P)) ∅ π.fwd collBad]
      ≤ Pr{let π ← $ᵗ PTable}[∃ n ∈ range qE, Ev n π] := prEvent_mono _ _ _ hcover
    _ ≤ ∑ n ∈ range qE, Pr{let π ← $ᵗ PTable}[Ev n π] := prEvent_exists_finset_le _ _ _
    _ ≤ ∑ n ∈ range qE, ((4 * n : ℕ) : ℝ≥0∞) * pE qE ^ 2 :=
        sum_le_sum fun n hn => (hstep n).resolve_right (by rw [mem_range] at hn; omega)
    _ = ((∑ n ∈ range qE, 4 * n : ℕ) : ℝ≥0∞) * pE qE ^ 2 := by rw [← sum_mul, Nat.cast_sum]
    _ ≤ ((2 * qE ^ 2 : ℕ) : ℝ≥0∞) * pE qE ^ 2 := by
        gcongr
        exact sum_range_four_mul_le qE
    _ = 2 * qE ^ 2 * pE qE ^ 2 := by push_cast; ring

end VoleMole.ROM.IC
