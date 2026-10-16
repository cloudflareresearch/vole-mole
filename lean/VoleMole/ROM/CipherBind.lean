import VoleMole.ROM.Basic
import VoleMole.ROM.FreshCache
import VoleMole.ZK.HopsIC

/-!
# Binding of the leaf commitments in the ideal-cipher model (plan M6, `ε_bind`)

`L0-L2-commitments.md` §4–§5: the leaf commitment of a key `k` of tree `i` is
`E_k(x₀) ‖ E_k(x₁)`, the cipher at the two CTR blocks `x₀ = iv ⊞ (0,0,0,i+L−1)` and `x₁ = x₀ ⊞ e₀`.
Binding (L1.2, "unique seeds") says that two keys with the same commitment do not both occur in the
prover's cipher queries, so that the key the verifier reconstructs from an opening is the one the
prover queried. Here this is proved for the executable BAVC reconstruction, with the cipher a
uniform table.

## The model

* **The cipher is a random oracle on cells** `(k, z) ↦ E_k(z)` (`cspec`, `CTable`): every row is a
  uniform *function* (the PRF view, as in the ZK hop H4, `ZK/IdealCipher.lean`). The verifier and
  the extractor read the table (`icPrg E.cipher`, the executable reconstruction with the ideal
  cipher); the prover is an adaptive computation `oa : OracleComp cspec α` that queries it, at most
  `n` times. Forward queries only: there are no inverse queries. The statement is for every
  prover with a fixed hash table and fixed coins (its hash queries answered by any fixed function);
  `ROM/CipherGame.lean` lifts it to the soundness game against the lazy hash oracle.
* **PRP vs PRF.** The switching lemma would cost `q_E²/2¹²⁹`, far more than the bound below, so it
  is not the route: in the permutation model with inverse queries the same argument goes through
  with `2⁻¹²⁸` per fresh answer replaced by `p = 1/(2¹²⁸ − q_E)` (a fresh forward or inverse answer
  is uniform over at least `2¹²⁸ − q_E` values; `L0-L2` §3.1). That version is not formalized.

## The collision event and its bound

* `collBad t c E` (the bad event of a fresh query `t = (k, w)` given the cache `c` of the earlier
  queries): for a neighbour `w'` of `w` (`adj w = {w ⊞ e₀, w ⊟ e₀}`, `nxt`, `prv`) with `(k, w')`
  not yet queried, some other key `κ` with one of `(κ, w)`, `(κ, w')` already queried has
  `E_κ(w) = E_k(w)` and `E_κ(w') = E_k(w')`. This is `L0-L2`'s double collision (C2), charged at
  the first query of the *second* key.
* **`pr_collBad_le`**: over the uncached cells, `Pr ≤ 2·N·2⁻²⁵⁶` for a cache of fewer than `N`
  cells (two neighbours, at most `N` keys `κ` with a cached cell there, and two fresh cells
  `(k, w)`, `(k, w')` hitting two values: `pr_two_cells_le`).
* **`prEvent_coll_le`**: an `n`-query prover meets a fresh `collBad` query with probability
  `≤ 2·n²·2⁻²⁵⁶ = n²·2⁻²⁵⁵` (`ROM/FreshCache.lean`, the union bound with a cache-reading bad
  event).
* **`freshBadC_of_two_keys`** (deterministic): two different keys, each queried by the prover at
  one of the two points of a leaf, with the same two blocks there, make some fresh query bad.

## Straight-line key extraction and binding

* `extractKey log E iv i a`: the key of the **first entry of the prover's cipher log** at one of the
  two points of tree `i` whose key has commitment `a` (the second block read from the table, i.e.
  evaluated by the extractor: `L0-L2` §6, Definition B). `keysOf`: these keys for the commitments
  that the reconstruction from the opening computes (at the hidden leaves, the opened ones).
* **`extractKey_eq_of_wit`**: outside the collision event, every logged witness of a commitment is
  the extracted key (L1.2; at a hidden leaf this is L2(c) without the "before `chal1`").
* **`binds_or_coll_or_dead`**: an opening (any `iv`, opening, `Δ`) whose reconstructed key at a
  non-hidden leaf differs from the extracted key either makes a fresh query bad, or opens a leaf
  whose key the prover never queried at either of that leaf's points (`DeadOpen`).
* **`prEvent_not_binds_le`**: `Pr_E[¬BindsIC] ≤ n²·2⁻²⁵⁵ + Pr_E[DeadOpen]`.

`DeadOpen` is what remains of `ε_bind`: a leaf opened with a key the prover never evaluated at
the leaf's points. Bounding it needs `L0-L2`'s linking (L1.4: the leaf commitments the verifier
recomputes are the `H₁` preimages committed before the chain's `H₂¹` query, events `Coll₁`,
`Hit₁`) and L2(a) (a committed leaf with no key evaluated before the chain is never opened,
`ε_dead`): ordering facts about the hash and cipher queries, as in the "same chain" step.
-/

open Finset OracleComp OracleSpec
open scoped ENNReal

namespace VoleMole.ROM.IC

open VoleMole.Prob VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK.Sim VoleMole.ROM

-- `cachedKeys c` filters all `2²⁵⁶` cells: it is never unfolded here (a hypothesis
-- `x ∈ cachedKeys c` must not be evaluated by `whnf` in the elaborator or the linters).
attribute [local irreducible] cachedKeys

/-! ## The ideal cipher as a random oracle on cells -/

/-- A cell of the cipher table: a key and an input block. -/
abbrev Cell := Blk × Blk

/-- **The cipher oracle**: a query `(k, z)` is answered by `E_k(z)`. -/
abbrev cspec : OracleSpec Cell := OracleSpec.ofFn fun _ : Cell => Blk

/-- A complete cipher table. -/
abbrev CTable := Cell → Blk

/-- The table as a `Cipher` (key ↦ row), the argument of `icPrg`. -/
def CTable.cipher (E : CTable) : Cipher := fun k z => E (k, z)

/-! ## The two points of a leaf commitment -/

/-- The CTR block after `w`: lane 0 plus one. -/
def nxt (w : Blk) : Blk := blk 16 (AES.ctrBlock (ba w) 1 0)

/-- The CTR block before `w`: lane 0 minus one. -/
def prv (w : Blk) : Blk := blk 16 (AES.ctrBlock (ba w) (0 - 1) 0)

/-- The two neighbours of a block. (Irreducible: `whnf` of a membership `x ∈ {nxt w, prv w}` would
try to decide the equality of the two blocks, which unfolds the CTR arithmetic.) -/
@[irreducible] def adj (w : Blk) : Finset Blk := {nxt w, prv w}

lemma mem_adj {w x : Blk} : x ∈ adj w ↔ x = nxt w ∨ x = prv w := by
  unfold adj
  rw [mem_insert, mem_singleton]

lemma card_adj_le (w : Blk) : (adj w).card ≤ 2 := by
  unfold adj
  exact card_le_two

lemma getLE32_ctrBlock (iv : ByteArray) (c t : UInt32) :
    AES.getLE32 (AES.ctrBlock iv c t) 0 = AES.getLE32 iv 0 + c ∧
      AES.getLE32 (AES.ctrBlock iv c t) 4 = AES.getLE32 iv 4 ∧
      AES.getLE32 (AES.ctrBlock iv c t) 8 = AES.getLE32 iv 8 ∧
      AES.getLE32 (AES.ctrBlock iv c t) 12 = AES.getLE32 iv 12 + t := by
  have s0 : (AES.pushLE32 ByteArray.empty (AES.getLE32 iv 0 + c)).size = 4 := by
    simp [size_pushLE32]
  set b0 := AES.pushLE32 ByteArray.empty (AES.getLE32 iv 0 + c)
  set b1 := AES.pushLE32 b0 (AES.getLE32 iv 4)
  have s1 : b1.size = 8 := by simp [b1, size_pushLE32, s0]
  set b2 := AES.pushLE32 b1 (AES.getLE32 iv 8)
  have s2 : b2.size = 12 := by simp [b2, size_pushLE32, s1]
  have e0 : AES.getLE32 b0 0 = AES.getLE32 iv 0 + c := by
    simpa using getLE32_pushLE32 ByteArray.empty (AES.getLE32 iv 0 + c)
  have e1 : AES.getLE32 b1 4 = AES.getLE32 iv 4 := by rw [← s0]; exact getLE32_pushLE32 _ _
  have e2 : AES.getLE32 b2 8 = AES.getLE32 iv 8 := by rw [← s1]; exact getLE32_pushLE32 _ _
  have e3 : AES.getLE32 (AES.pushLE32 b2 (AES.getLE32 iv 12 + t)) 12 = AES.getLE32 iv 12 + t := by
    rw [← s2]; exact getLE32_pushLE32 _ _
  show AES.getLE32 (AES.pushLE32 b2 (AES.getLE32 iv 12 + t)) 0 = _ ∧
    AES.getLE32 (AES.pushLE32 b2 (AES.getLE32 iv 12 + t)) 4 = _ ∧
    AES.getLE32 (AES.pushLE32 b2 (AES.getLE32 iv 12 + t)) 8 = _ ∧
    AES.getLE32 (AES.pushLE32 b2 (AES.getLE32 iv 12 + t)) 12 = _
  refine ⟨?_, ?_, ?_, e3⟩
  · rw [getLE32_pushLE32_of_lt _ _ _ (by omega), getLE32_pushLE32_of_lt _ _ _ (by omega),
      getLE32_pushLE32_of_lt _ _ _ (by omega), e0]
  · rw [getLE32_pushLE32_of_lt _ _ _ (by omega), getLE32_pushLE32_of_lt _ _ _ (by omega), e1]
  · rw [getLE32_pushLE32_of_lt _ _ _ (by omega), e2]

/-- **CTR blocks compose**: counters and tweaks add. -/
lemma ctrBlock_ctrBlock (iv : ByteArray) (c t c' t' : UInt32) :
    AES.ctrBlock (AES.ctrBlock iv c t) c' t' = AES.ctrBlock iv (c + c') (t + t') := by
  have e : ∀ (b : ByteArray) (c t : UInt32), AES.ctrBlock b c t =
      AES.pushLE32 (AES.pushLE32 (AES.pushLE32 (AES.pushLE32 ByteArray.empty
        (AES.getLE32 b 0 + c)) (AES.getLE32 b 4)) (AES.getLE32 b 8)) (AES.getLE32 b 12 + t) :=
    fun _ _ _ => rfl
  obtain ⟨h0, h4, h8, h12⟩ := getLE32_ctrBlock iv c t
  rw [e (AES.ctrBlock iv c t), h0, h4, h8, h12, e iv, add_assoc, add_assoc]

lemma ne_of_getLE32_add {w : Blk} {d : UInt32} (hd : d ≠ 0)
    (h : blk 16 (AES.ctrBlock (ba w) d 0) = w) : False := by
  have h' := congrArg (fun b : Blk => AES.getLE32 (ba b) 0) h
  simp only [ba_blk_of_size (ctrBlock_size _ _ _), (getLE32_ctrBlock _ _ _).1] at h'
  have h'' := congrArg UInt32.toNat h'
  have hd' : d.toNat ≠ 0 := fun h0 => hd (UInt32.toNat_inj.1 (by simpa using h0))
  rw [UInt32.toNat_add] at h''
  have := (AES.getLE32 (ba w) 0).toNat_lt
  have := d.toNat_lt
  omega

lemma nxt_ne (w : Blk) : nxt w ≠ w := ne_of_getLE32_add (by decide)

lemma prv_ne (w : Blk) : prv w ≠ w := ne_of_getLE32_add (by decide)

lemma not_mem_adj (w : Blk) : w ∉ adj w := by
  rw [mem_adj, not_or]
  exact ⟨(nxt_ne w).symm, (prv_ne w).symm⟩

/-- **The two points of the leaf commitments of tree `i`** under `iv`: block `c ∈ {0, 1}` of
`PRG(key, iv, i + L − 1)` (`BAVC.leafCom`). -/
def lp (iv : ByteArray) (i c : ℕ) : Blk :=
  blk 16 (AES.ctrBlock iv (0 + c.toUInt32) (i + BAVC.numLeaves - 1).toUInt32)

lemma nxt_lp (iv : ByteArray) (i : ℕ) : nxt (lp iv i 0) = lp iv i 1 := by
  simp only [nxt, lp, ba_blk_of_size (ctrBlock_size _ _ _), ctrBlock_ctrBlock, add_zero]
  rfl

lemma prv_lp (iv : ByteArray) (i : ℕ) : prv (lp iv i 1) = lp iv i 0 := by
  simp only [prv, lp, ba_blk_of_size (ctrBlock_size _ _ _), ctrBlock_ctrBlock, add_zero]
  rfl

lemma lp1_mem_adj (iv : ByteArray) (i : ℕ) : lp iv i 1 ∈ adj (lp iv i 0) :=
  mem_adj.2 (Or.inl (nxt_lp iv i).symm)

lemma lp0_mem_adj (iv : ByteArray) (i : ℕ) : lp iv i 0 ∈ adj (lp iv i 1) :=
  mem_adj.2 (Or.inr (prv_lp iv i).symm)

lemma lp_ne (iv : ByteArray) (i : ℕ) : lp iv i 0 ≠ lp iv i 1 := by
  rw [← nxt_lp]; exact (nxt_ne _).symm

/-- **The leaf commitment under the ideal cipher** is the key's row at the two points. -/
lemma leafCom_ic (E : Cipher) (iv : ByteArray) (k : Blk) (i : ℕ) :
    @BAVC.leafCom (icPrg E) iv (ba k) i = ba (E k (lp iv i 0)) ++ ba (E k (lp iv i 1)) := by
  show @HasPrg.prg (icPrg E) (ba k) iv (i + BAVC.numLeaves - 1).toUInt32 0 2 = _
  rw [icPrg_prg, prgR_two]
  rfl

lemma ba_append_inj {u v u' v' : Blk} (h : ba u ++ ba v = ba u' ++ ba v') : u = u' ∧ v = v' := by
  constructor
  · funext t
    have := congrArg (fun b : ByteArray => b.get! t) h
    simpa only [get!_ba_append, t.isLt, ↓reduceIte, get!_ba _ t.isLt] using this
  · funext t
    have := congrArg (fun b : ByteArray => b.get! (t + 16)) h
    simpa only [get!_ba_append, show ¬ t.val + 16 < 16 by omega, ↓reduceIte,
      Nat.add_sub_cancel, get!_ba _ t.isLt] using this

/-! ## The collision event -/

/-- **The bad event of a fresh cipher query** `t = (k, w)`, given the cache `c` of the earlier
queries: for a neighbour `w'` of `w` with `(k, w')` not yet queried, another key `κ`, queried
before at `w` or at `w'`, has the same two values `E_κ(w) = E_k(w)`, `E_κ(w') = E_k(w')`. -/
def collBad (t : Cell) (c : cspec.QueryCache) (E : CTable) : Prop :=
  ∃ w' ∈ adj t.2, ∃ κ : Blk, κ ≠ t.1 ∧ c (t.1, w') = none ∧
    ((c (κ, t.2)).isSome ∨ (c (κ, w')).isSome) ∧ E (κ, t.2) = E (t.1, t.2) ∧
      E (κ, w') = E (t.1, w')

/-- **Two fresh cells hitting two values**: for uncached cells `a ≠ b` and cells `a'`, `b'` other
than `a`, `b`, the completed table has `E(a') = E(a)` and `E(b') = E(b)` with probability at most
`2⁻²⁵⁶`. (The tables with the property, with `a`, `b` overwritten, inject into all tables.) -/
theorem pr_two_cells_le (c : cspec.QueryCache) {a b a' b' : Cell} (hab : a ≠ b) (ha : c a = none)
    (hb : c b = none) (ha'a : a' ≠ a) (ha'b : a' ≠ b) (hb'a : b' ≠ a) (hb'b : b' ≠ b) :
    Pr{let g ← $ᵗ CTable}[completeTable c g a' = completeTable c g a ∧
      completeTable c g b' = completeTable c g b] ≤ (2 ^ 256)⁻¹ := by
  classical
  rw [SampleableType.prEvent_uniformSample]
  let P : CTable → Prop := fun g =>
    completeTable c g a' = completeTable c g a ∧ completeTable c g b' = completeTable c g b
  have hca : ∀ g : CTable, completeTable c g a = g a := fun g => by simp [completeTable, ha]
  have hcb : ∀ g : CTable, completeTable c g b = g b := fun g => by simp [completeTable, hb]
  let Ψ : {g // P g} × Blk × Blk → CTable := fun x =>
    Function.update (Function.update x.1.1 a x.2.1) b x.2.2
  have hΨ : Function.Injective Ψ := by
    rintro ⟨⟨g, hg⟩, u, v⟩ ⟨⟨g', hg'⟩, u', v'⟩ h
    simp only [Ψ] at h
    have hv : v = v' := by simpa using congrFun h b
    have hu : u = u' := by
      have := congrFun h a
      simpa [Function.update_of_ne hab] using this
    have hoff : ∀ d, d ≠ a → d ≠ b → g d = g' d := fun d hda hdb => by
      have := congrFun h d
      simpa [Function.update_of_ne hda, Function.update_of_ne hdb] using this
    have hcomp : ∀ d, d ≠ a → d ≠ b → completeTable c g d = completeTable c g' d :=
      fun d hda hdb => by simp only [completeTable, hoff d hda hdb]
    have hga : g a = g' a := by
      rw [← hca g, ← hca g', ← hg.1, ← hg'.1, hcomp a' ha'a ha'b]
    have hgb : g b = g' b := by
      rw [← hcb g, ← hcb g', ← hg.2, ← hg'.2, hcomp b' hb'a hb'b]
    have hgg : g = g' := by
      funext d
      by_cases hda : d = a
      · subst hda; exact hga
      by_cases hdb : d = b
      · subst hdb; exact hgb
      exact hoff d hda hdb
    subst hgg hu hv
    rfl
  have hcard := Fintype.card_le_of_injective Ψ hΨ
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_subtype, card_blk] at hcard
  have hT0 : (Fintype.card CTable : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [ENNReal.div_le_iff hT0 (ENNReal.natCast_ne_top _), ← ENNReal.div_eq_inv_mul,
    ENNReal.le_div_iff_mul_le (Or.inl (pow_ne_zero _ two_ne_zero))
      (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top))]
  have : ((univ.filter P).card : ℝ≥0∞) * 2 ^ 256 =
      (((univ.filter P).card * (2 ^ 128 * 2 ^ 128) : ℕ) : ℝ≥0∞) := by
    push_cast; ring
  rw [this]
  exact_mod_cast hcard

open Classical in
/-- The pairs `(w', κ)` (a neighbour of `w` and another key) over which `collBad (k, w) c` ranges:
`(k, w')` uncached, and `κ` cached at `w` or at `w'`. -/
@[irreducible] noncomputable def collPairs (c : cspec.QueryCache) (k w : Blk) : Finset (Blk × Blk) :=
  ((adj w) ×ˢ univ).filter fun p =>
    p.2 ≠ k ∧ c (k, p.1) = none ∧ ((c (p.2, w)).isSome ∨ (c (p.2, p.1)).isSome)

lemma mem_collPairs {c : cspec.QueryCache} {k w : Blk} {p : Blk × Blk} :
    p ∈ collPairs c k w ↔ p.1 ∈ adj w ∧ p.2 ≠ k ∧ c (k, p.1) = none ∧
      ((c (p.2, w)).isSome ∨ (c (p.2, p.1)).isSome) := by
  unfold collPairs
  rw [mem_filter, mem_product]
  simp only [mem_univ, and_true]

lemma mem_cachedKeys {c : cspec.QueryCache} {d : Cell} : d ∈ cachedKeys c ↔ (c d).isSome := by
  unfold cachedKeys
  rw [mem_filter]
  simp only [mem_univ, true_and]

/-- A cached cell of the key of a pair `(w', κ)` of `collPairs c k w`, at `w` or at `w'`. -/
def pairCell (c : cspec.QueryCache) (w : Blk) (p : Blk × Blk) : Blk × Cell :=
  (p.1, if (c (p.2, w)).isSome then (p.2, w) else (p.2, p.1))

lemma pairCell_injOn (c : cspec.QueryCache) (k w : Blk) :
    Set.InjOn (pairCell c w) (collPairs c k w) := by
  rintro ⟨w₁, κ₁⟩ - ⟨w₂, κ₂⟩ - h
  simp only [pairCell, Prod.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  have : κ₁ = κ₂ := by
    split_ifs at h
    · exact (Prod.mk.inj h).1
    · exact (Prod.mk.inj h).1
    · exact (Prod.mk.inj h).1
    · exact (Prod.mk.inj h).1
  rw [this]

lemma pairCell_mem (c : cspec.QueryCache) (k w : Blk) :
    ∀ p ∈ collPairs c k w, pairCell c w p ∈ (adj w) ×ˢ cachedKeys c := by
  intro p hp
  obtain ⟨hw', -, -, hs⟩ := mem_collPairs.1 hp
  rw [mem_product]
  refine ⟨hw', ?_⟩
  show (if (c (p.2, w)).isSome then (p.2, w) else (p.2, p.1)) ∈ cachedKeys c
  split_ifs with h
  · exact mem_cachedKeys.2 h
  · exact mem_cachedKeys.2 (hs.resolve_left h)

/-- At most two neighbours, and at most `|cache|` keys with a cached cell at them. -/
lemma card_collPairs_le (c : cspec.QueryCache) (k w : Blk) :
    (collPairs c k w).card ≤ 2 * (cachedKeys c).card :=
  calc (collPairs c k w).card ≤ ((adj w) ×ˢ cachedKeys c).card :=
        card_le_card_of_injOn _ (pairCell_mem c k w) (pairCell_injOn c k w)
    _ = (adj w).card * (cachedKeys c).card := card_product _ _
    _ ≤ 2 * (cachedKeys c).card := Nat.mul_le_mul_right _ (card_adj_le w)

/-- **The bound of a fresh query's collision event**: for a cache `c` without `t` and with fewer
than `N` cells, `collBad t` has probability at most `2·N·2⁻²⁵⁶` over the uncached cells. -/
theorem pr_collBad_le (c : cspec.QueryCache) (t : Cell) (ht : c t = none) {N : ℕ}
    (hN : (cachedKeys c).card < N) :
    Pr{let g ← $ᵗ CTable}[collBad t c (completeTable c g)] ≤ 2 * N * (2 ^ 256)⁻¹ := by
  obtain ⟨k, w⟩ := t
  have hsub : ∀ g : CTable, collBad (k, w) c (completeTable c g) →
      ∃ p ∈ collPairs c k w, completeTable c g (p.2, w) = completeTable c g (k, w) ∧
        completeTable c g (p.2, p.1) = completeTable c g (k, p.1) := by
    rintro g ⟨w', hw', κ, hκ, hn, hs, h1, h2⟩
    exact ⟨(w', κ), mem_collPairs.2 ⟨hw', hκ, hn, hs⟩, h1, h2⟩
  have hterm : ∀ p ∈ collPairs c k w, Pr{let g ← $ᵗ CTable}[
      completeTable c g (p.2, w) = completeTable c g (k, w) ∧
        completeTable c g (p.2, p.1) = completeTable c g (k, p.1)] ≤ (2 ^ 256)⁻¹ := by
    intro p hp
    obtain ⟨hw', hκ, hn, -⟩ := mem_collPairs.1 hp
    have hww : w ≠ p.1 := fun h => by
      rw [← h] at hw'
      exact not_mem_adj w hw'
    exact pr_two_cells_le c (a := (k, w)) (b := (k, p.1)) (a' := (p.2, w)) (b' := (p.2, p.1))
      (fun h => hww (congrArg Prod.snd h)) ht hn (fun h => hκ (congrArg Prod.fst h))
      (fun h => hκ (congrArg Prod.fst h)) (fun h => hκ (congrArg Prod.fst h))
      (fun h => hκ (congrArg Prod.fst h))
  have h1 := prEvent_mono ($ᵗ CTable) _ _ hsub
  have h2 := prEvent_exists_finset_le_card_mul (collPairs c k w) ($ᵗ CTable) _ hterm
  have hc : ((collPairs c k w).card : ℝ≥0∞) ≤ 2 * N := by
    have := (card_collPairs_le c k w).trans (Nat.mul_le_mul_left 2 hN.le)
    exact_mod_cast this
  exact h1.trans (h2.trans (by gcongr))

/-- **The collision bound**: an `n`-query prover meets a fresh query in its collision event with
probability at most `2·n²·2⁻²⁵⁶ = n²·2⁻²⁵⁵`, for any event `P` of the table that implies one
(`htrace`). -/
theorem prEvent_coll_le {α : Type} (oa : OracleComp cspec α) (n : ℕ) (hn : IsTotalQueryBound oa n)
    (P : CTable → Prop) (htrace : ∀ E, P E → freshBadC oa ∅ E collBad) :
    Pr{let E ← $ᵗ CTable}[P E] ≤ 2 * n ^ 2 * (2 ^ 256)⁻¹ := by
  have h := prEvent_le_of_freshBadC oa n hn collBad (2 * n * (2 ^ 256)⁻¹)
    (fun c t ht hc => pr_collBad_le c t ht hc) P htrace
  refine h.trans (le_of_eq ?_)
  ring

/-! ## Two keys with one commitment -/

/-- `κ` is queried by the log at one of the points `x₀`, `x₁`. -/
def HasCell (log : QueryLog cspec) (κ x₀ x₁ : Blk) : Prop :=
  ∃ q ∈ log, q.1 = (κ, x₀) ∨ q.1 = (κ, x₁)

lemma exists_first {β : Type} (P : β → Prop) [DecidablePred P] :
    ∀ l : List β, (∃ x ∈ l, P x) → ∃ pre x post, l = pre ++ x :: post ∧ P x ∧ ∀ y ∈ pre, ¬P y
  | [], ⟨_, h, _⟩ => absurd h (List.not_mem_nil)
  | y :: l, h => by
    by_cases hy : P y
    · exact ⟨[], y, l, rfl, hy, by simp⟩
    · obtain ⟨x, hx, hPx⟩ := h
      rcases List.mem_cons.1 hx with rfl | hx
      · exact absurd hPx hy
      obtain ⟨pre, x', post, rfl, hP, hpre⟩ := exists_first P l ⟨x, hx, hPx⟩
      refine ⟨y :: pre, x', post, rfl, hP, fun z hz => ?_⟩
      rcases List.mem_cons.1 hz with rfl | hz
      exacts [hy, hpre z hz]

/-- The collision charged at the first query of the second key: `q` is the first query of `κb`
at the leaf's points, and `κa` was queried there before. -/
lemma collBad_of_second {x₀ x₁ : Blk} (h01 : x₁ ∈ adj x₀) (h10 : x₀ ∈ adj x₁) {κa κb : Blk}
    (hne : κa ≠ κb) (E : CTable) (heq0 : E (κa, x₀) = E (κb, x₀))
    (heq1 : E (κa, x₁) = E (κb, x₁)) (pre : QueryLog cspec) (q : (_ : Cell) × Blk)
    (hq : q.1 = (κb, x₀) ∨ q.1 = (κb, x₁))
    (hpre : ∀ y ∈ pre, ¬(y.1 = (κb, x₀) ∨ y.1 = (κb, x₁)))
    (ha : ∃ y ∈ pre, y.1 = (κa, x₀) ∨ y.1 = (κa, x₁)) :
    collBad q.1 (cacheOfLog ∅ pre) E := by
  have hnone : ∀ d, (∀ y ∈ pre, y.1 ≠ d) → cacheOfLog (∅ : cspec.QueryCache) pre d = none :=
    fun d hd => (cacheOfLog_eq_none _ _ _).2 ⟨rfl, hd⟩
  have hsome : ∀ d, (∃ y ∈ pre, y.1 = d) → (cacheOfLog (∅ : cspec.QueryCache) pre d).isSome :=
    fun d ⟨y, hy, hyd⟩ => by
      rw [Option.isSome_iff_ne_none, ne_eq, cacheOfLog_eq_none]
      exact fun h => h.2 y hy hyd
  obtain ⟨y, hy, hya⟩ := ha
  rcases hq with hq | hq <;> rw [hq]
  · refine ⟨x₁, h01, κa, hne, hnone _ fun y hy h => hpre y hy (Or.inr h), ?_, heq0, heq1⟩
    rcases hya with h | h
    · exact Or.inl (hsome _ ⟨y, hy, h⟩)
    · exact Or.inr (hsome _ ⟨y, hy, h⟩)
  · refine ⟨x₀, h10, κa, hne, hnone _ fun y hy h => hpre y hy (Or.inl h), ?_, heq1, heq0⟩
    rcases hya with h | h
    · exact Or.inr (hsome _ ⟨y, hy, h⟩)
    · exact Or.inl (hsome _ ⟨y, hy, h⟩)

/-- **Two keys queried at a leaf's points with equal blocks there make a fresh query bad.** -/
theorem freshBadC_of_two_keys {α : Type} (oa : OracleComp cspec α) (E : CTable) {x₀ x₁ : Blk}
    (h01 : x₁ ∈ adj x₀) (h10 : x₀ ∈ adj x₁) {κ₁ κ₂ : Blk} (hne : κ₁ ≠ κ₂)
    (h₁ : HasCell (tableQueryLog oa E) κ₁ x₀ x₁) (h₂ : HasCell (tableQueryLog oa E) κ₂ x₀ x₁)
    (heq0 : E (κ₁, x₀) = E (κ₂, x₀)) (heq1 : E (κ₁, x₁) = E (κ₂, x₁)) :
    freshBadC oa ∅ E collBad := by
  classical
  rw [freshBadC_empty_iff]
  obtain ⟨p₁, y₁, s₁, e₁, hy₁, hp₁⟩ := exists_first (fun y : (_ : Cell) × Blk =>
    y.1 = (κ₁, x₀) ∨ y.1 = (κ₁, x₁)) _ h₁
  obtain ⟨p₂, y₂, s₂, e₂, hy₂, hp₂⟩ := exists_first (fun y : (_ : Cell) × Blk =>
    y.1 = (κ₂, x₀) ∨ y.1 = (κ₂, x₁)) _ h₂
  have hkey : ∀ y : (_ : Cell) × Blk, (y.1 = (κ₁, x₀) ∨ y.1 = (κ₁, x₁)) →
      ¬(y.1 = (κ₂, x₀) ∨ y.1 = (κ₂, x₁)) := by
    rintro y (h | h) (h' | h') <;> rw [h] at h' <;> simp_all
  rcases List.append_eq_append_iff.1 (e₁.symm.trans e₂) with ⟨a', hp, hs⟩ | ⟨c', hp, hs⟩
  · -- `p₂ = p₁ ++ a'`: the first `κ₁` query comes first; charge `y₂`.
    cases a' with
    | nil =>
      simp only [List.append_nil, List.nil_append, List.cons.injEq] at hp hs
      exact absurd (hs.1 ▸ hy₂) (hkey _ hy₁)
    | cons z a' =>
      simp only [List.cons_append, List.cons.injEq] at hs
      refine ⟨p₂, y₂, s₂, e₂, fun p hp h => hp₂ p hp (h ▸ hy₂), ?_⟩
      exact collBad_of_second h01 h10 hne E heq0 heq1 p₂ y₂ hy₂ hp₂
        ⟨y₁, by rw [hp, hs.1]; simp, hy₁⟩
  · -- `p₁ = p₂ ++ c'`: the first `κ₂` query comes first; charge `y₁`.
    cases c' with
    | nil =>
      simp only [List.append_nil, List.nil_append, List.cons.injEq] at hp hs
      exact absurd (hs.1 ▸ hy₁) (fun h => hkey _ h hy₂)
    | cons z c' =>
      simp only [List.cons_append, List.cons.injEq] at hs
      refine ⟨p₁, y₁, s₁, e₁, fun p hp h => hp₁ p hp (h ▸ hy₁), ?_⟩
      exact collBad_of_second h01 h10 hne.symm E heq0.symm heq1.symm p₁ y₁ hy₁ hp₁
        ⟨y₂, by rw [hp, hs.1]; simp, hy₂⟩

/-! ## Straight-line extraction of the leaf keys -/

/-- **The extracted key of a commitment** `a` (32 bytes) of tree `i` under `iv`: the key of the
first entry of the prover's cipher log `log` at one of the tree's two leaf points whose key `κ`
has commitment `a`, that is `E_κ(x₀) ‖ E_κ(x₁) = a` (the logged block and the other one read from
the table: the extractor evaluates the partner block, Definition B of `L0-L2` §3.4). -/
def extractKey (log : QueryLog cspec) (E : CTable) (iv : ByteArray) (i : ℕ) (a : ByteArray) :
    Option Blk :=
  (log.find? fun q => decide ((q.1.2 = lp iv i 0 ∨ q.1.2 = lp iv i 1) ∧
    ba (E (q.1.1, lp iv i 0)) ++ ba (E (q.1.1, lp iv i 1)) = a)).map (·.1.1)

/-- The 32-byte commitment of leaf `(i, j)` in the leaves' concatenated commitments. -/
def comAt (coms : ByteArray) (i j : ℕ) : ByteArray :=
  coms.extract (32 * (BAVC.leafOffset i + j)) (32 * (BAVC.leafOffset i + j) + 32)

/-- **The extractor's leaf keys** for an opening: the extracted keys of the commitments that the
reconstruction (with the ideal cipher `E`) computes from the opening, the opened ones at the hidden
leaves; zero where no key is found, and outside the leaf indices `i < τ`, `j < 2^{k_i}`. Computed
from the proof, the prover's cipher log and the table. -/
def keysOf (log : QueryLog cspec) (E : CTable) (iv opening delta : ByteArray) :
    ℕ → ℕ → ByteArray :=
  match @BAVC.reconstruct (icPrg E.cipher) iv opening delta with
  | some leaves => fun i j =>
      if i < BAVC.tau ∧ j < 2 ^ BAVC.kOf i then
        ((extractKey log E iv i (comAt leaves.coms i j)).map ba).getD BAVC.zeroBlock
      else BAVC.zeroBlock
  | none => fun _ _ => BAVC.zeroBlock

/-- The extractor's key at a leaf index. -/
lemma keysOf_of_reconstruct {log : QueryLog cspec} {E : CTable} {iv opening delta : ByteArray}
    {leaves : BAVC.Leaves} (hr : @BAVC.reconstruct (icPrg E.cipher) iv opening delta = some leaves)
    {i j : ℕ} (hi : i < BAVC.tau) (hj : j < 2 ^ BAVC.kOf i) :
    keysOf log E iv opening delta i j =
      ((extractKey log E iv i (comAt leaves.coms i j)).map ba).getD BAVC.zeroBlock := by
  unfold keysOf
  rw [hr]
  exact ite_eq_left ⟨hi, hj⟩

/-- The extractor's keys vanish outside the leaf indices. -/
lemma keysOf_of_not_valid (log : QueryLog cspec) (E : CTable) (iv opening delta : ByteArray)
    {i j : ℕ} (h : ¬(i < BAVC.tau ∧ j < 2 ^ BAVC.kOf i)) :
    keysOf log E iv opening delta i j = BAVC.zeroBlock := by
  unfold keysOf
  cases @BAVC.reconstruct (icPrg E.cipher) iv opening delta with
  | some leaves => exact ite_eq_right h
  | none => rfl

/-- **Outside the collision event, a logged witness is the extracted key**: if `κ` was queried at
one of tree `i`'s leaf points and has commitment `a`, the extractor returns `κ` (L1.2, unique
seeds; at a hidden leaf, L2(c)). -/
theorem extractKey_eq_of_wit {α : Type} (oa : OracleComp cspec α) (E : CTable)
    (hcoll : ¬freshBadC oa ∅ E collBad) (iv : ByteArray) (i : ℕ) {κ : Blk}
    (hκ : HasCell (tableQueryLog oa E) κ (lp iv i 0) (lp iv i 1)) :
    extractKey (tableQueryLog oa E) E iv i (ba (E (κ, lp iv i 0)) ++ ba (E (κ, lp iv i 1))) =
      some κ := by
  set log := tableQueryLog oa E
  set a := ba (E (κ, lp iv i 0)) ++ ba (E (κ, lp iv i 1))
  let pr : (_ : Cell) × Blk → Bool := fun q => decide ((q.1.2 = lp iv i 0 ∨ q.1.2 = lp iv i 1) ∧
    ba (E (q.1.1, lp iv i 0)) ++ ba (E (q.1.1, lp iv i 1)) = a)
  obtain ⟨q, hq, hqκ⟩ := hκ
  have hpq : pr q = true := by
    simp only [pr, decide_eq_true_eq]
    rcases hqκ with h | h <;> rw [h] <;> simp [a]
  obtain ⟨q₀, hfind⟩ : ∃ q₀, log.find? pr = some q₀ := Option.isSome_iff_exists.1
    (List.find?_isSome.2 ⟨q, hq, hpq⟩)
  have hq₀ : pr q₀ = true := List.find?_some hfind
  have hmem : q₀ ∈ log := List.mem_of_find?_eq_some hfind
  simp only [pr, decide_eq_true_eq] at hq₀
  obtain ⟨hpt, hcom⟩ := hq₀
  have hκ₀ : q₀.1.1 = κ := by
    by_contra hne
    obtain ⟨h0, h1⟩ := ba_append_inj hcom
    apply hcoll
    refine freshBadC_of_two_keys oa E (lp1_mem_adj iv i) (lp0_mem_adj iv i) hne
      ⟨q₀, hmem, ?_⟩ ⟨q, hq, hqκ⟩ h0 h1
    rcases hpt with h | h
    · exact Or.inl (Prod.ext rfl h)
    · exact Or.inr (Prod.ext rfl h)
  simp only [extractKey]
  rw [show (fun q : (_ : Cell) × Blk => decide ((q.1.2 = lp iv i 0 ∨ q.1.2 = lp iv i 1) ∧
    ba (E (q.1.1, lp iv i 0)) ++ ba (E (q.1.1, lp iv i 1)) = a)) = pr from rfl, hfind]
  simp [hκ₀]

/-! ## Binding of the reconstruction -/

/-- The commitment of a non-hidden leaf of the reconstruction is the leaf commitment of its key. -/
lemma comAt_reconstruct [HasPrg] {iv opening delta : ByteArray} {leaves : BAVC.Leaves}
    (h : BAVC.reconstruct iv opening delta = some leaves) {i j : ℕ} (hi : i < BAVC.tau)
    (hj : j < 2 ^ BAVC.kOf i) (hjd : j ≠ BAVC.deltaIndex delta i) :
    comAt leaves.coms i j = BAVC.leafCom iv (leafKey leaves i j) i := by
  rw [leafKey_reconstruct h hi hj hjd]
  rw [reconstruct_eq] at h
  split_ifs at h with hb
  cases h
  rw [Bool.not_eq_true] at hb
  have hsz := (badOpening_false hb).1
  unfold comAt
  rw [leavesOf_eq]
  have hne : (some (BAVC.deltaIndex delta i) == some j) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq, Option.some.injEq]; exact Ne.symm hjd
  rw [extract_pieces _ 32 (fun i' hi' j' hj' => by
      split
      · rw [ByteArray.size_extract, hsz]
        have hi'' : i' < 17 := hi'
        show min (32 * i' + 32) (17 * 32 + 105 * 16) - 32 * i' = 32
        omega
      · exact leafCom_size _ _ _) hi hj]
  simp only [hne, Bool.false_eq_true, ↓reduceIte]

/-- The reconstructed keys off the hidden leaves are 16-byte blocks. -/
lemma leafKey_size [HasPrg] {iv opening delta : ByteArray} {leaves : BAVC.Leaves}
    (h : BAVC.reconstruct iv opening delta = some leaves) {i j : ℕ} (hi : i < BAVC.tau)
    (hj : j < 2 ^ BAVC.kOf i) (hjd : j ≠ BAVC.deltaIndex delta i) :
    (leafKey leaves i j).size = 16 := by
  rw [leafKey_reconstruct h hi hj hjd]
  have h' := h
  rw [reconstruct_eq] at h'
  split_ifs at h' with hb
  rw [Bool.not_eq_true] at hb
  exact recTree_size hb (treePos_lt hi hj)

/-- **Binding of the opening** to the extractor's keys (`ROM/Accept.lean`'s `Binds`, for the
ideal-cipher reconstruction at `iv`): every non-hidden leaf key of the reconstruction is the
corresponding key of `keys`. -/
def BindsIC (E : CTable) (iv opening delta : ByteArray) (keys : ℕ → ℕ → ByteArray) : Prop :=
  ∀ leaves, @BAVC.reconstruct (icPrg E.cipher) iv opening delta = some leaves →
    ∀ i < BAVC.tau, ∀ j < 2 ^ BAVC.kOf i, j ≠ BAVC.deltaIndex delta i →
      leafKey leaves i j = keys i j

/-- **A dead leaf is opened**: some non-hidden leaf key of the reconstruction was queried by the
prover at neither of its leaf's points. -/
def DeadOpen (log : QueryLog cspec) (E : CTable) (iv opening delta : ByteArray) : Prop :=
  ∃ leaves, @BAVC.reconstruct (icPrg E.cipher) iv opening delta = some leaves ∧
    ∃ i < BAVC.tau, ∃ j < 2 ^ BAVC.kOf i, j ≠ BAVC.deltaIndex delta i ∧
      ¬HasCell log (blk 16 (leafKey leaves i j)) (lp iv i 0) (lp iv i 1)

/-- **Binding, deterministically**: if the opening does not bind to the extracted keys, then the
prover's log has a fresh collision query, or a dead leaf is opened. -/
theorem binds_or_coll_or_dead {α : Type} (oa : OracleComp cspec α) (E : CTable)
    (iv opening delta : ByteArray) :
    BindsIC E iv opening delta (keysOf (tableQueryLog oa E) E iv opening delta) ∨
      freshBadC oa ∅ E collBad ∨ DeadOpen (tableQueryLog oa E) E iv opening delta := by
  let _ : HasPrg := icPrg E.cipher
  by_cases hcoll : freshBadC oa ∅ E collBad
  · exact Or.inr (Or.inl hcoll)
  by_cases hdead : DeadOpen (tableQueryLog oa E) E iv opening delta
  · exact Or.inr (Or.inr hdead)
  left
  intro leaves hr i hi j hj hjd
  have hlive : HasCell (tableQueryLog oa E) (blk 16 (leafKey leaves i j)) (lp iv i 0)
      (lp iv i 1) := by
    by_contra h
    exact hdead ⟨leaves, hr, i, hi, j, hj, hjd, h⟩
  have hsz := leafKey_size hr hi hj hjd
  have hcom : comAt leaves.coms i j = ba (E (blk 16 (leafKey leaves i j), lp iv i 0)) ++
      ba (E (blk 16 (leafKey leaves i j), lp iv i 1)) := by
    rw [comAt_reconstruct hr hi hj hjd, ← ba_blk_of_size hsz, leafCom_ic, ba_blk_of_size hsz]
    rfl
  have hk := extractKey_eq_of_wit oa E hcoll iv i hlive
  rw [← hcom] at hk
  rw [keysOf_of_reconstruct hr hi hj, hk]
  exact (ba_blk_of_size hsz).symm

/-- **The binding bound in the ideal-cipher model.** For a prover `oa` making at most `n` cipher
queries and outputting `iv`, an opening and `Δ` (`inp`), the opening fails to bind to the extracted
keys with probability at most `n²·2⁻²⁵⁵` plus the probability that a dead leaf is opened. -/
theorem prEvent_not_binds_le {α : Type} (oa : OracleComp cspec α) (n : ℕ)
    (hn : IsTotalQueryBound oa n) (inp : α → ByteArray × ByteArray × ByteArray) :
    Pr{let E ← $ᵗ CTable}[¬BindsIC E (inp (evalWithAnswerFn (QueryImpl.ofFn E) oa)).1
      (inp (evalWithAnswerFn (QueryImpl.ofFn E) oa)).2.1
      (inp (evalWithAnswerFn (QueryImpl.ofFn E) oa)).2.2
      (keysOf (tableQueryLog oa E) E (inp (evalWithAnswerFn (QueryImpl.ofFn E) oa)).1
        (inp (evalWithAnswerFn (QueryImpl.ofFn E) oa)).2.1
        (inp (evalWithAnswerFn (QueryImpl.ofFn E) oa)).2.2)] ≤
      2 * n ^ 2 * (2 ^ 256)⁻¹ +
        Pr{let E ← $ᵗ CTable}[DeadOpen (tableQueryLog oa E) E
          (inp (evalWithAnswerFn (QueryImpl.ofFn E) oa)).1
          (inp (evalWithAnswerFn (QueryImpl.ofFn E) oa)).2.1
          (inp (evalWithAnswerFn (QueryImpl.ofFn E) oa)).2.2] := by
  set D : CTable → Prop := fun E => DeadOpen (tableQueryLog oa E) E
    (inp (evalWithAnswerFn (QueryImpl.ofFn E) oa)).1
    (inp (evalWithAnswerFn (QueryImpl.ofFn E) oa)).2.1
    (inp (evalWithAnswerFn (QueryImpl.ofFn E) oa)).2.2 with hD
  have hC := prEvent_coll_le oa n hn (fun E => freshBadC oa ∅ E collBad) fun _ h => h
  have hor := prEvent_or_le ($ᵗ CTable) (fun E => freshBadC oa ∅ E collBad) D
  have h1 := prEvent_mono ($ᵗ CTable) _ (fun E => freshBadC oa ∅ E collBad ∨ D E)
    (fun E h => (binds_or_coll_or_dead oa E _ _ _).resolve_left h)
  have h2 := hor.trans (add_le_add hC le_rfl)
  exact h1.trans h2

end VoleMole.ROM.IC
