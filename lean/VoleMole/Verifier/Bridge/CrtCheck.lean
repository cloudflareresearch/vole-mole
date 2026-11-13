import VoleMole.ZK.CrtMask

/-!
# Bridge: the CRT VOLE identity, checked in the kernel

`CrtComplete` (`Bridge/Prover.lean`: the verifier's CRT masks are `ṽ_mask + u_mask·Δ'`) comes down
to the bilinear identity that defines faest-arch-opt's tables (`CrtGen.identityOk`, checked there
at run time): for `Δ = e_c` (`c = p_i + b`, bit `b` of small VOLE `i`) and every mask `a`,

  `L_c(a) := Σ_{d < k_i} r_d W_tree[p_i + d] + Σ_{e < 312} G[e]_c ⟨F[e], a⟩ W_gate[e] = a · W_crt[c]`,

where `r_d = Σ_{t < k_i} (X^{b+t} mod M_i)_d · u_{i,t}` is bit `d` of the CRT product of `Δ_i = X^b`
with the mask's residue `u_i` (its `u_low` bits, `u_{i,t} = ⟨maskInv[p_i + t], a⟩` by the
certificate of `ZK/CrtMask.lean`). Both sides are `F₂`-linear in `a`, so it suffices to check the
`128 · 120` pairs `(c, X^k)` (**`Lc_eq`**).

The check (`crtCheck`, `decide +kernel`) packs, for each `c`, the 128 values `L_c(X^k)` into one
`2¹⁶³⁸⁴`-bit number (slot `k` at bits `128 k …`; `slot`), as XORs of outer products
`w · spread v` (`mul_spread`: `spread v` puts bit `k` of `v` at bit `128 k`), and compares with the
packed `X^k · W_crt[c]` (`rhsPacked`, iterated multiplication by `X` on numbers, `mulXN`). The
tables enter as numbers (`CrtData` holds hex literals, so the kernel parses no strings), the
`X^s mod M_i` as the verifier computes them (`polyMod`, `pmTab`).

* `slot_gatePacked`, `slot_treePackedAt`, `slot_rhsPacked`: what slot `k` holds.
* `natGF`, `gfNat`, `gf_eq_sum`, `natGF_mulXN`, `basis_mul`: numbers `< 2¹²⁸` as field elements;
  `mulXN` is multiplication by `X` (checked on the 128 monomials, both sides linear), and
  `X^k = natGF 2^k`.
* `formHom_basis`: `⟨l, X^k⟩ = l_k`. `Lc_basis`: `L_c(X^k)` is slot `k` of the packed left-hand
  side.
-/

namespace VoleMole.Verifier.Bridge.CrtCheck

open VoleMole.Verifier VoleMole.Arith VoleMole.Verifier.Bridge

/-- `Σ_{a ∈ l} f a` over `F₂`-vectors (`Nat`s, XOR). -/
def xorSum {α : Type} (l : List α) (f : α → ℕ) : ℕ := l.foldl (fun acc a => acc ^^^ f a) 0

/-- The 128 × 128 matrix with row `k` equal to `w` if bit `k` of `v` is set (row `k` at bits
`128 k …`). -/
def outer (v w : ℕ) : ℕ := xorSum (List.range 128) fun k => if v.testBit k then w <<< (128 * k) else 0

/-- `Σ_{k < 128, v_k} 2^{128 k}`; `w · spread v = outer v w` for `w < 2¹²⁸`. -/
def spread (v : ℕ) : ℕ := xorSum (List.range 128) fun k => if v.testBit k then 2 ^ (128 * k) else 0

/-- `CrtGen.transposeRow` on the list of rows. -/
def trRow (M : List ℕ) (j : ℕ) : ℕ := (M.foldl (fun (x : ℕ × ℕ) row =>
  (if row.testBit j then x.1 ||| (1 <<< x.2) else x.1, x.2 + 1)) (0, 0)).1

/-- `Σ_{e < |L|, P e} L[e]`, walking `L` once. -/
def xorSel (P : ℕ → Bool) (L : List ℕ) : ℕ :=
  (L.foldl (fun (x : ℕ × ℕ) o => (if P x.2 then x.1 ^^^ o else x.1, x.2 + 1)) (0, 0)).1

/-- `X^s mod M_i`, as the verifier computes it (`s < 16`), for the 17 trees. -/
def pmTab : List (List ℕ) := (List.range 17).map fun i => (List.range 16).map fun s =>
  (polyMod ((1 : UInt64) <<< s.toUInt64) (CrtGen.moduli.getD i 0).toUInt64).toNat

/-- The rows of `W_tree`, `W_crt` (as `CrtGen.tables` stores them). -/
def wtL : List ℕ := (List.range 120).map (trRow CrtGen.wTree.toList)
def wcL : List ℕ := (List.range 120).map (trRow CrtGen.wCrt.toList)
/-- `spread` of the rows of `ZK.maskInv`. -/
def invSpreads : List ℕ := ZK.maskInv.map spread

/-- `F[e] ⊗ W_gate[e]`, `e < 312`. -/
def gateOuters : List ℕ := List.zipWith (fun f w => w * spread f) CrtGen.F.toList
  ((List.range 312).map (trRow CrtGen.wGate.toList))

/-- The gate part of `L_c` on the 128 basis vectors (packed). -/
def gatePacked (c : ℕ) : ℕ := xorSel (trRow CrtGen.G.toList c).testBit gateOuters

/-- The tree part of `L_c` on the 128 basis vectors (packed): for `c = p_i + b`,
`Σ_{d < k_i} ρ_{c,d} ⊗ W_tree[p_i + d]` with `ρ_{c,d} = Σ_{t < k_i, (X^{b+t} mod M_i)_d} maskInv[p_i + t]`. -/
def treePacked (c : ℕ) : ℕ :=
  let i := BAVC.treeOf c
  let o := BAVC.bitOffset i
  let k := BAVC.kOf i
  let pms := ((pmTab.getD i []).drop (c - o)).take k
  let sps := (invSpreads.drop o).take k
  xorSel (fun _ => true) ((List.range k).zipWith (fun d w =>
    w * xorSel (fun t => (pms.getD t 0).testBit d) sps) ((wtL.drop o).take k))

/-- Multiplication by `X` in `GF(2¹²⁸)` on numbers `< 2¹²⁸`. -/
def mulXN (x : ℕ) : ℕ := (x <<< 1) % 2 ^ 128 ^^^ (if x.testBit 127 then 0x87 else 0)

/-- `X^k · W_crt[c]`, `k < 128` (packed). -/
def rhsPacked (d : ℕ) : ℕ :=
  ((List.range 128).foldl (fun (x : ℕ × ℕ) k => (x.1 ^^^ (x.2 <<< (128 * k)), mulXN x.2)) (0, d)).1

/-- The identity on all basis pairs. -/
def crtCheck : Bool :=
  ((List.range 120).zip wcL).all fun x => (gatePacked x.1 ^^^ treePacked x.1) == rhsPacked x.2

/-- **The certificate holds** (kernel computation, ≈ 1 min and 4 GB). -/
theorem crtCheck_eq : crtCheck = true := by decide +kernel

/-! ## Numbers as bit vectors -/

lemma xorSum_nil {α : Type} (f : α → ℕ) : xorSum [] f = 0 := rfl

lemma xorSum_append_single {α : Type} (l : List α) (a : α) (f : α → ℕ) :
    xorSum (l ++ [a]) f = xorSum l f ^^^ f a := by
  simp [xorSum, List.foldl_append]

lemma foldl_xor_start {α : Type} (f : α → ℕ) : ∀ (l : List α) (x : ℕ),
    l.foldl (fun acc a => acc ^^^ f a) x = x ^^^ l.foldl (fun acc a => acc ^^^ f a) 0
  | [], x => by simp
  | a :: l, x => by
    simp only [List.foldl_cons]
    rw [foldl_xor_start f l (x ^^^ f a), foldl_xor_start f l (0 ^^^ f a), Nat.zero_xor,
      Nat.xor_assoc]

lemma xorSum_cons {α : Type} (a : α) (l : List α) (f : α → ℕ) :
    xorSum (a :: l) f = f a ^^^ xorSum l f := by
  simp only [xorSum, List.foldl_cons, Nat.zero_xor]
  exact foldl_xor_start f l (f a)

lemma xorSum_lt {α : Type} (l : List α) (f : α → ℕ) {m : ℕ} (h : ∀ a ∈ l, f a < 2 ^ m) :
    xorSum l f < 2 ^ m := by
  induction l with
  | nil => simp [xorSum_nil]
  | cons a l ih =>
    rw [xorSum_cons]
    exact Nat.xor_lt_two_pow (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

/-- A linear map of bit vectors commutes with `xorSum`. -/
lemma map_xorSum {α : Type} (φ : ℕ → ℕ) (h0 : φ 0 = 0) (hx : ∀ x y, φ (x ^^^ y) = φ x ^^^ φ y)
    (l : List α) (f : α → ℕ) : φ (xorSum l f) = xorSum l (φ ∘ f) := by
  induction l with
  | nil => exact h0
  | cons a l ih => rw [xorSum_cons, xorSum_cons, hx, ih]; rfl

lemma testBit_xorSum {α : Type} (l : List α) (f : α → ℕ) (n : ℕ) :
    zb ((xorSum l f).testBit n) = (l.map fun a => zb ((f a).testBit n)).sum := by
  induction l with
  | nil => simp [xorSum_nil]
  | cons a l ih => rw [xorSum_cons, Nat.testBit_xor, zb_xor, ih]; simp

lemma xorSum_congr {α : Type} {l : List α} {f g : α → ℕ} (h : ∀ a ∈ l, f a = g a) :
    xorSum l f = xorSum l g := by
  simp only [xorSum]
  exact List.foldl_ext _ _ _ fun acc a ha => by rw [h a ha]

/-- `2^m b + a = 2^m b ⊕ a` for `a < 2^m`. -/
lemma add_eq_xor_of_lt {a b m : ℕ} (ha : a < 2 ^ m) : 2 ^ m * b + a = 2 ^ m * b ^^^ a := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_xor, Nat.testBit_two_pow_mul]
  by_cases hj : j < m
  · simp [hj, show ¬ j ≥ m by omega]
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    simp [hj, show j ≥ m by omega]

/-- **The packed outer product is a product**: `w · spread v = outer v w` for `w < 2¹²⁸`. -/
theorem mul_spread {w : ℕ} (hw : w < 2 ^ 128) (v : ℕ) : w * spread v = outer v w := by
  have key : ∀ N, w * xorSum (List.range N) (fun k => if v.testBit k then 2 ^ (128 * k) else 0) =
      xorSum (List.range N) (fun k => if v.testBit k then w <<< (128 * k) else 0) ∧
      xorSum (List.range N) (fun k => if v.testBit k then 2 ^ (128 * k) else 0) < 2 ^ (128 * N) ∧
      xorSum (List.range N) (fun k => if v.testBit k then w <<< (128 * k) else 0) < 2 ^ (128 * N) := by
    intro N
    induction N with
    | zero => simp [xorSum_nil]
    | succ N ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      simp only [List.range_succ, xorSum_append_single]
      have hle : 2 ^ (128 * N) * 2 ^ 128 = 2 ^ (128 * (N + 1)) := by rw [← pow_add]; ring_nf
      by_cases hv : v.testBit N
      · simp only [hv, ↓reduceIte]
        have e1 : xorSum (List.range N) (fun k => if v.testBit k then 2 ^ (128 * k) else 0) ^^^
            2 ^ (128 * N) = 2 ^ (128 * N) * 1 +
              xorSum (List.range N) (fun k => if v.testBit k then 2 ^ (128 * k) else 0) := by
          rw [add_eq_xor_of_lt h2, Nat.xor_comm, Nat.mul_one]
        have e2 : xorSum (List.range N) (fun k => if v.testBit k then w <<< (128 * k) else 0) ^^^
            w <<< (128 * N) = 2 ^ (128 * N) * w +
              xorSum (List.range N) (fun k => if v.testBit k then w <<< (128 * k) else 0) := by
          rw [add_eq_xor_of_lt h3, Nat.xor_comm, Nat.shiftLeft_eq, Nat.mul_comm]
        refine ⟨?_, ?_, ?_⟩
        · rw [e1, e2, Nat.mul_add, h1]; ring
        · rw [e1]
          calc 2 ^ (128 * N) * 1 + _ < 2 ^ (128 * N) * 1 + 2 ^ (128 * N) := by omega
            _ ≤ 2 ^ (128 * (N + 1)) := by rw [← hle]; nlinarith [Nat.one_le_two_pow (n := 128 * N)]
        · rw [e2]
          calc 2 ^ (128 * N) * w + _ < 2 ^ (128 * N) * w + 2 ^ (128 * N) := by omega
            _ = 2 ^ (128 * N) * (w + 1) := by ring
            _ ≤ 2 ^ (128 * N) * 2 ^ 128 := Nat.mul_le_mul_left _ hw
            _ = _ := hle
      · simp only [hv, Bool.false_eq_true, ↓reduceIte, Nat.xor_zero]
        refine ⟨h1, lt_of_lt_of_le h2 ?_, lt_of_lt_of_le h3 ?_⟩ <;>
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  exact (key 128).1

/-! ## Slots of packed vectors -/

/-- Slot `k` (bits `128 k … 128 k + 127`). -/
def slot (x k : ℕ) : ℕ := (x >>> (128 * k)) % 2 ^ 128

lemma slot_xor (x y k : ℕ) : slot (x ^^^ y) k = slot x k ^^^ slot y k := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [slot, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_xor]
  by_cases hj : j < 128 <;> simp [hj]

lemma slot_zero (k : ℕ) : slot 0 k = 0 := by simp [slot]

lemma slot_xorSum {α : Type} (l : List α) (f : α → ℕ) (k : ℕ) :
    slot (xorSum l f) k = xorSum l fun a => slot (f a) k :=
  map_xorSum (fun x => slot x k) (slot_zero k) (fun x y => slot_xor x y k) l f

lemma slot_ite (P : Prop) [Decidable P] (x k : ℕ) :
    slot (if P then x else 0) k = if P then slot x k else 0 := by
  split <;> simp [slot_zero]

lemma slot_shift {w : ℕ} (hw : w < 2 ^ 128) (j k : ℕ) :
    slot (w <<< (128 * j)) k = if j = k then w else 0 := by
  apply Nat.eq_of_testBit_eq
  intro s
  simp only [slot, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
  split_ifs with h
  · subst h
    by_cases hs : s < 128
    · simp [hs]
    · simp [hs, Nat.testBit_lt_two_pow (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by norm_num)
        (show 128 ≤ s by omega)))]
  · simp only [Nat.zero_testBit]
    by_cases hs : s < 128
    · simp only [hs, decide_true, Bool.true_and]
      rcases Nat.lt_or_gt_of_ne h with h' | h'
      · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by norm_num)
          (by omega)))]
        simp
      · simp [show ¬ 128 * k + s ≥ 128 * j by omega]
    · simp [hs]

lemma xorSum_range_single {n k : ℕ} (hk : k < n) (f : ℕ → ℕ) :
    xorSum (List.range n) (fun j => if j = k then f j else 0) = f k := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, xorSum_append_single]
    by_cases h : k = n
    · subst h
      have : xorSum (List.range k) (fun j => if j = k then f j else 0) = 0 := by
        rw [xorSum_congr (g := fun _ => 0) fun j hj => by
          simp [show j ≠ k by have := List.mem_range.1 hj; omega]]
        induction (List.range k) with
        | nil => rfl
        | cons a l ih' => rw [xorSum_cons, ih']; rfl
      simp [this]
    · rw [ih (by omega)]; simp [Ne.symm h]

/-- Slot `k` of `w · spread v` is `w` if bit `k` of `v` is set. -/
theorem slot_mul_spread {w : ℕ} (hw : w < 2 ^ 128) (v : ℕ) {k : ℕ} (hk : k < 128) :
    slot (w * spread v) k = if v.testBit k then w else 0 := by
  rw [mul_spread hw, outer, slot_xorSum]
  simp only [slot_ite, slot_shift hw]
  rw [xorSum_congr (g := fun j => if j = k then (if v.testBit j then w else 0) else 0) fun j _ => by
    split_ifs <;> simp_all]
  exact xorSum_range_single hk _

lemma xorSum_map {α β : Type} (l : List α) (g : α → β) (f : β → ℕ) :
    xorSum (l.map g) f = xorSum l (f ∘ g) := by
  simp [xorSum, List.foldl_map]

lemma xorSel_spec (P : ℕ → Bool) : ∀ (L : List ℕ) (acc n : ℕ),
    L.foldl (fun (x : ℕ × ℕ) o => (if P x.2 then x.1 ^^^ o else x.1, x.2 + 1)) (acc, n) =
      (acc ^^^ xorSum (List.range L.length) (fun e => if P (n + e) then L.getD e 0 else 0),
        n + L.length)
  | [], acc, n => by simp [xorSum_nil]
  | o :: L, acc, n => by
    rw [List.foldl_cons, xorSel_spec P L]
    simp only [List.length_cons, List.range_succ_eq_map, xorSum_cons, xorSum_map]
    refine Prod.ext ?_ (by simp; omega)
    simp only [Nat.add_zero, List.getD_cons_zero]
    rw [show (fun e => if P (n + e) then (o :: L).getD e 0 else 0) ∘ Nat.succ =
      fun e => if P (n + 1 + e) then L.getD e 0 else 0 from funext fun e => by
        simp [Nat.add_assoc, Nat.add_comm 1 e]]
    split <;> simp [Nat.xor_assoc]

/-- `xorSel` as a sum. -/
theorem xorSel_eq (P : ℕ → Bool) (L : List ℕ) :
    xorSel P L = xorSum (List.range L.length) fun e => if P e then L.getD e 0 else 0 := by
  rw [xorSel, xorSel_spec]; simp

lemma trRow_lt (M : List ℕ) (j : ℕ) : trRow M j < 2 ^ M.length := by
  have key : ∀ (L : List ℕ) (x : ℕ × ℕ), x.1 < 2 ^ x.2 →
      (L.foldl (fun (x : ℕ × ℕ) row =>
        (if row.testBit j then x.1 ||| (1 <<< x.2) else x.1, x.2 + 1)) x).1 < 2 ^ (x.2 + L.length) ∧
      (L.foldl (fun (x : ℕ × ℕ) row =>
        (if row.testBit j then x.1 ||| (1 <<< x.2) else x.1, x.2 + 1)) x).2 = x.2 + L.length := by
    intro L
    induction L with
    | nil => intro x h; simpa using h
    | cons r L ih =>
      intro x h
      rw [List.foldl_cons]
      have h' : (if r.testBit j then x.1 ||| (1 <<< x.2) else x.1) < 2 ^ (x.2 + 1) := by
        have h2 : x.1 < 2 ^ (x.2 + 1) := lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by omega))
        split
        · refine Nat.or_lt_two_pow h2 ?_
          rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
        · exact h2
      obtain ⟨h1, h2⟩ := ih (_, x.2 + 1) h'
      rw [List.length_cons, show x.2 + (L.length + 1) = x.2 + 1 + L.length by omega]
      exact ⟨h1, h2⟩
  have := (key M (0, 0) (by norm_num)).1
  simpa [trRow] using this

lemma trRow_lt128 {M : Array ℕ} (h : M.size = 128) (j : ℕ) : trRow M.toList j < 2 ^ 128 := by
  have := trRow_lt M.toList j; rwa [Array.length_toList, h] at this

lemma wTree_size : CrtGen.wTree.size = 128 := by decide +kernel
lemma wGate_size : CrtGen.wGate.size = 128 := by decide +kernel
lemma wCrt_size : CrtGen.wCrt.size = 128 := by decide +kernel
lemma F_length : CrtGen.F.toList.length = 312 := by decide +kernel
lemma maskInv_length : ZK.maskInv.length = 128 := by decide +kernel

lemma gateOuters_length : gateOuters.length = 312 := by
  simp only [gateOuters, List.length_zipWith, F_length, List.length_map, List.length_range,
    Nat.min_self]

lemma gateOuters_getD {e : ℕ} (he : e < 312) :
    gateOuters.getD e 0 = trRow CrtGen.wGate.toList e * spread (CrtGen.F.toList.getD e 0) := by
  rw [List.getD_eq_getElem?_getD, gateOuters, List.getElem?_zipWith,
    List.getElem?_eq_getElem (by rw [F_length]; exact he), List.getElem?_map,
    List.getElem?_range he, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [F_length]; exact he)]
  rfl

/-- **Slot `k` of the gate part.** -/
theorem slot_gatePacked (c : ℕ) {k : ℕ} (hk : k < 128) :
    slot (gatePacked c) k = xorSum (List.range 312) fun e =>
      if (trRow CrtGen.G.toList c).testBit e && (CrtGen.F.toList.getD e 0).testBit k then
        trRow CrtGen.wGate.toList e else 0 := by
  rw [gatePacked, xorSel_eq, gateOuters_length, slot_xorSum]
  refine xorSum_congr fun e he => ?_
  have he := List.mem_range.1 he
  rw [slot_ite, gateOuters_getD he, slot_mul_spread (trRow_lt128 wGate_size e) _ hk]
  cases (trRow CrtGen.G.toList c).testBit e <;> cases (CrtGen.F.toList.getD e 0).testBit k <;> rfl

lemma getD_take_drop (L : List ℕ) (a n t : ℕ) (ht : t < n) :
    ((L.drop a).take n).getD t 0 = L.getD (a + t) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, ht, ↓reduceIte, List.getElem?_drop]

lemma length_take_drop (L : List ℕ) {a n : ℕ} (h : a + n ≤ L.length) :
    ((L.drop a).take n).length = n := by
  simp only [List.length_take, List.length_drop]; omega

lemma xorSum_xor {α : Type} (l : List α) (f g : α → ℕ) :
    xorSum l (fun a => f a ^^^ g a) = xorSum l f ^^^ xorSum l g := by
  induction l with
  | nil => simp [xorSum_nil]
  | cons a l ih =>
    simp only [xorSum_cons, ih]
    ac_rfl

lemma spread_xor (x y : ℕ) : spread (x ^^^ y) = spread x ^^^ spread y := by
  simp only [spread, ← xorSum_xor]
  refine xorSum_congr fun k _ => ?_
  rw [Nat.testBit_xor]
  cases x.testBit k <;> cases y.testBit k <;> simp

lemma spread_zero : spread 0 = 0 := by
  simp only [spread, Nat.zero_testBit, Bool.false_eq_true, ↓reduceIte]
  induction (List.range 128) with
  | nil => rfl
  | cons a l ih => rw [xorSum_cons, ih]; rfl

/-- `X^s mod M_i` from the table. -/
def pmVal (i s : ℕ) : ℕ := (pmTab.getD i []).getD s 0

/-- `ρ_{c,d}` (see `treePacked`). -/
def rho (c d : ℕ) : ℕ :=
  let i := BAVC.treeOf c
  let o := BAVC.bitOffset i
  xorSum (List.range (BAVC.kOf i)) fun t =>
    if (pmVal i (c - o + t)).testBit d then ZK.maskInv.getD (o + t) 0 else 0

lemma tree_bounds {c : ℕ} (hc : c < 120) :
    BAVC.bitOffset (BAVC.treeOf c) + BAVC.kOf (BAVC.treeOf c) ≤ 120 ∧
      c - BAVC.bitOffset (BAVC.treeOf c) < BAVC.kOf (BAVC.treeOf c) ∧
      BAVC.kOf (BAVC.treeOf c) ≤ 8 := by
  obtain ⟨h1, h2, h3⟩ := treeOf_spec hc
  have := pos_lt h1 (show BAVC.kOf (BAVC.treeOf c) - 1 < BAVC.kOf (BAVC.treeOf c) by
    rw [kOf_eq]; split <;> omega)
  refine ⟨by omega, h3, by rw [kOf_eq]; split <;> omega⟩

lemma wtL_length : wtL.length = 120 := by simp [wtL]
lemma invSpreads_length : invSpreads.length = 128 := by simp [invSpreads, maskInv_length]

lemma invSpreads_getD {j : ℕ} (hj : j < 128) : invSpreads.getD j 0 = spread (ZK.maskInv.getD j 0) := by
  rw [invSpreads, List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [maskInv_length]; omega)]
  simp only [Option.map_some, Option.getD_some]

/-- `treePacked` at tree `i` (offset `o`, `kk` bits), bit `b`. -/
def treePackedAt (i o kk b : ℕ) : ℕ :=
  xorSel (fun _ => true) ((List.range kk).zipWith (fun d w =>
    w * xorSel (fun t => ((((pmTab.getD i []).drop b).take kk).getD t 0).testBit d)
      ((invSpreads.drop o).take kk)) ((wtL.drop o).take kk))

lemma treePacked_eq (c : ℕ) : treePacked c = treePackedAt (BAVC.treeOf c)
    (BAVC.bitOffset (BAVC.treeOf c)) (BAVC.kOf (BAVC.treeOf c)) (c - BAVC.bitOffset (BAVC.treeOf c)) :=
  rfl

lemma slot_treePackedAt {i o kk b k : ℕ} (hb1 : o + kk ≤ 120) (hk : k < 128) :
    slot (treePackedAt i o kk b) k = xorSum (List.range kk) fun d =>
      if (xorSum (List.range kk) fun t => if ((pmTab.getD i []).getD (b + t) 0).testBit d then
        ZK.maskInv.getD (o + t) 0 else 0).testBit k then wtL.getD (o + d) 0 else 0 := by
  have hwts : ((wtL.drop o).take kk).length = kk := length_take_drop _ (by rw [wtL_length]; omega)
  have hsps : ((invSpreads.drop o).take kk).length = kk :=
    length_take_drop _ (by rw [invSpreads_length]; omega)
  rw [treePackedAt, xorSel_eq, List.length_zipWith, List.length_range, hwts, Nat.min_self,
    slot_xorSum]
  refine xorSum_congr fun d hd => ?_
  have hd := List.mem_range.1 hd
  simp only [↓reduceIte]
  rw [List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_range hd,
    List.getElem?_eq_getElem (by rw [hwts]; exact hd)]
  simp only [Option.getD_some]
  have hw : ((wtL.drop o).take kk)[d]'(by rw [hwts]; exact hd) = wtL.getD (o + d) 0 := by
    rw [← getD_take_drop wtL o kk d hd, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [hwts]; exact hd)]
    rfl
  rw [hw, xorSel_eq, hsps]
  rw [xorSum_congr (g := fun t => spread (if ((pmTab.getD i []).getD (b + t) 0).testBit d then
      ZK.maskInv.getD (o + t) 0 else 0)) fun t ht => by
    have ht := List.mem_range.1 ht
    rw [getD_take_drop _ _ _ _ ht, getD_take_drop _ _ _ _ ht, invSpreads_getD (by omega)]
    split
    · rfl
    · exact spread_zero.symm]
  rw [← Function.comp_def spread, ← map_xorSum spread spread_zero spread_xor, slot_mul_spread _ _ hk]
  rw [List.getD_eq_getElem?_getD, wtL, List.getElem?_map,
    List.getElem?_range (show o + d < 120 by omega)]
  exact trRow_lt128 wTree_size _

/-- Multiplication by `X` stays below `2¹²⁸`. -/
lemma mulXN_lt (x : ℕ) : mulXN x < 2 ^ 128 := by
  refine Nat.xor_lt_two_pow (Nat.mod_lt _ (by norm_num)) ?_
  split <;> norm_num

lemma iterate_mulXN_lt {x : ℕ} (hx : x < 2 ^ 128) : ∀ j, mulXN^[j] x < 2 ^ 128
  | 0 => hx
  | j + 1 => by rw [Function.iterate_succ_apply']; exact mulXN_lt _

/-- **Slot `k` of the right-hand side** is `X^k · δ`. -/
theorem slot_rhsPacked {x : ℕ} (hx : x < 2 ^ 128) {k : ℕ} (hk : k < 128) :
    slot (rhsPacked x) k = mulXN^[k] x := by
  have key : ∀ N, (List.range N).foldl (fun (y : ℕ × ℕ) j => (y.1 ^^^ (y.2 <<< (128 * j)), mulXN y.2))
      (0, x) = (xorSum (List.range N) fun j => mulXN^[j] x <<< (128 * j), mulXN^[N] x) := by
    intro N
    induction N with
    | zero => rfl
    | succ N ih =>
      rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil,
        xorSum_append_single, Function.iterate_succ_apply']
  rw [rhsPacked, key, slot_xorSum]
  simp only [slot_shift (iterate_mulXN_lt hx _)]
  exact xorSum_range_single hk _

/-! ## Numbers as field elements -/

/-- A number `< 2¹²⁸` as a field element (bit `k` = coefficient of `X^k`). -/
def natGF (x : ℕ) : GF128 := (CrtGen.w128OfNat x).toGF

lemma natGF_xor (x y : ℕ) : natGF (x ^^^ y) = natGF x + natGF y := by
  rw [natGF, ZK.w128OfNat_xor, toGF_xor]; rfl

lemma natGF_zero : natGF 0 = 0 := rfl

lemma natGF_xorSum {α : Type} (l : List α) (f : α → ℕ) :
    natGF (xorSum l f) = (l.map fun a => natGF (f a)).sum := by
  induction l with
  | nil => simp [xorSum_nil, natGF_zero]
  | cons a l ih => rw [xorSum_cons, natGF_xor, ih]; simp

lemma natGF_ite (P : Prop) [Decidable P] (x : ℕ) :
    natGF (if P then x else 0) = if P then natGF x else 0 := by
  split <;> rfl

/-- A field element as a number (bit `k` = coefficient of `X^k`). -/
def gfNat (a : GF128) : ℕ := a.lo.toNat + 2 ^ 64 * a.hi.toNat

lemma zb_inj' {x y : Bool} (h : zb x = zb y) : x = y := by
  cases x <;> cases y <;> simp_all [zb]

lemma gfNat_lt (a : GF128) : gfNat a < 2 ^ 128 := by
  have h1 := a.lo.toNat_lt; have h2 := a.hi.toNat_lt
  simp only [gfNat]; omega

lemma natGF_gfNat (a : GF128) : natGF (gfNat a) = a := by
  have h1 := a.lo.toNat_lt; have h2 := a.hi.toNat_lt
  simp only [natGF, gfNat, CrtGen.w128OfNat, W128.toGF]
  have e1 : (a.lo.toNat + 2 ^ 64 * a.hi.toNat) % 2 ^ 64 = a.lo.toNat := by omega
  have e2 : (a.lo.toNat + 2 ^ 64 * a.hi.toNat) / 2 ^ 64 % 2 ^ 64 = a.hi.toNat := by omega
  rw [e1, e2]
  simp

/-- A number `< 2¹²⁸` is the sum of its bits. -/
lemma eq_xorSum_bits {x : ℕ} (hx : x < 2 ^ 128) :
    x = xorSum (List.range 128) fun k => if x.testBit k then 2 ^ k else 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  apply zb_inj'
  rw [testBit_xorSum, list_sum_range]
  by_cases hj : j < 128
  · rw [Finset.sum_eq_single j (fun k _ hk => by
        split <;> simp [hk]) (by simp [hj])]
    split <;> simp_all
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    refine (Finset.sum_eq_zero fun k hk => ?_).symm
    have hk := Finset.mem_range.1 hk
    split <;> simp [show k ≠ j by omega]

/-- **Every field element is the sum of its monomials.** -/
theorem gf_eq_sum (a : GF128) :
    a = ∑ k ∈ Finset.range 128, if (gfNat a).testBit k then natGF (2 ^ k) else 0 := by
  conv_lhs => rw [← natGF_gfNat a, eq_xorSum_bits (gfNat_lt a)]
  rw [natGF_xorSum, list_sum_range]
  simp only [natGF_ite]

lemma mulX_eq (a : GF128) : GF128.mulX a = ⟨2, 0⟩ * a := by
  apply GF128.eval_injective
  rw [GF128.eval_mulX GF128.isRoot_root, GF128.eval_mul GF128.isRoot_root, GF128.eval_X]

lemma mulX_add (a b : GF128) : GF128.mulX (a + b) = GF128.mulX a + GF128.mulX b := by
  rw [mulX_eq, mulX_eq, mulX_eq, mul_add]

lemma iterate_mulX_mul (a b : GF128) : ∀ k, GF128.mulX^[k] (a * b) = GF128.mulX^[k] a * b
  | 0 => rfl
  | k + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', iterate_mulX_mul a b k,
      mulX_eq, mulX_eq, mul_assoc]

lemma mulXN_xor (x y : ℕ) : mulXN (x ^^^ y) = mulXN x ^^^ mulXN y := by
  have h1 : ((x ^^^ y) <<< 1) % 2 ^ 128 = (x <<< 1) % 2 ^ 128 ^^^ (y <<< 1) % 2 ^ 128 := by
    apply Nat.eq_of_testBit_eq
    intro j
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_shiftLeft]
    by_cases hj : j < 128 <;> by_cases hj1 : 1 ≤ j <;> simp [hj, hj1]
  have h2 : (if (x ^^^ y).testBit 127 then 0x87 else 0) =
      (if x.testBit 127 then 0x87 else 0) ^^^ (if y.testBit 127 then 0x87 else 0) := by
    rw [Nat.testBit_xor]; cases x.testBit 127 <;> cases y.testBit 127 <;> simp
  rw [mulXN, mulXN, mulXN, h1, h2]
  ac_rfl

lemma mulXN_zero : mulXN 0 = 0 := rfl

lemma mulXN_basis : ∀ k < 128, natGF (mulXN (2 ^ k)) = GF128.mulX (natGF (2 ^ k)) := by
  decide +kernel

/-- **`mulXN` is multiplication by `X`.** -/
theorem natGF_mulXN {x : ℕ} (hx : x < 2 ^ 128) : natGF (mulXN x) = GF128.mulX (natGF x) := by
  rw [eq_xorSum_bits hx, map_xorSum mulXN mulXN_zero mulXN_xor, natGF_xorSum, natGF_xorSum]
  have hmap : ∀ (l : List ℕ), GF128.mulX ((l.map fun k =>
      natGF (if x.testBit k then 2 ^ k else 0)).sum) =
      (l.map fun k => GF128.mulX (natGF (if x.testBit k then 2 ^ k else 0))).sum := by
    intro l
    induction l with
    | nil => simp only [List.map_nil, List.sum_nil, mulX_eq, mul_zero]
    | cons k l ih => simp only [List.map_cons, List.sum_cons, mulX_add, ih]
  rw [hmap]
  congr 1
  refine List.map_congr_left fun k hk => ?_
  have hk := List.mem_range.1 hk
  simp only [Function.comp_apply]
  split
  · exact mulXN_basis k hk
  · rfl

lemma natGF_iterate {x : ℕ} (hx : x < 2 ^ 128) :
    ∀ k, natGF (mulXN^[k] x) = GF128.mulX^[k] (natGF x)
  | 0 => rfl
  | k + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      natGF_mulXN (iterate_mulXN_lt hx k), natGF_iterate hx k]

/-- `X^k · a = mulX^k a`, with `X^k = natGF 2^k`. -/
lemma basis_mul {k : ℕ} (hk : k < 128) (a : GF128) :
    natGF (2 ^ k) * a = GF128.mulX^[k] a := by
  have hb : ∀ k < 128, natGF (2 ^ k) = GF128.mulX^[k] 1 := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ← ih (by omega), ← natGF_mulXN (Nat.pow_lt_pow_right
        (by norm_num) (by omega))]
      congr 1
      have h127 : (2 ^ k).testBit 127 = false := by
        rw [Nat.testBit_two_pow]; exact decide_eq_false (by omega)
      rw [mulXN, h127, Nat.shiftLeft_eq, ← pow_succ,
        Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))]
      simp
  rw [hb k hk, ← iterate_mulX_mul, one_mul]

/-! ## The identity for all `u_mask` -/

lemma and_two_pow (n k : ℕ) : n &&& 2 ^ k = if n.testBit k then 2 ^ k else 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  by_cases h : k = j
  · subst h; split <;> simp_all
  · split <;> simp [h]

lemma par_two_pow : ∀ k < 64, par (2 ^ k) = true := by decide +kernel

lemma par_zero : par 0 = false := rfl

lemma natGF_lo (x : ℕ) : (natGF x).lo.toNat = x % 2 ^ 64 := by
  simp [natGF, CrtGen.w128OfNat, W128.toGF, Nat.toUInt64]

lemma natGF_hi (x : ℕ) : (natGF x).hi.toNat = x / 2 ^ 64 % 2 ^ 64 := by
  simp [natGF, CrtGen.w128OfNat, W128.toGF, Nat.toUInt64]

/-- `⟨l, X^k⟩ = l_k`. -/
theorem formHom_basis (l : ℕ) {k : ℕ} (hk : k < 128) :
    formHom l (natGF (2 ^ k)) = zb (l.testBit k) := by
  show zb (form l (natGF (2 ^ k))) = _
  congr 1
  simp only [form, natGF_lo, natGF_hi]
  by_cases hk64 : k < 64
  · rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hk64),
      Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hk64), Nat.zero_mod, Nat.and_zero,
      par_zero, Bool.xor_false, and_two_pow, Nat.testBit_mod_two_pow]
    by_cases hl : l.testBit k
    · simp [hl, hk64, par_two_pow k hk64]
    · simp [hl, par_zero]
  · have e1 : 2 ^ k % 2 ^ 64 = 0 := by
      rw [show k = 64 + (k - 64) by omega, pow_add, Nat.mul_mod_right]
    have e2 : 2 ^ k / 2 ^ 64 % 2 ^ 64 = 2 ^ (k - 64) := by
      rw [show k = 64 + (k - 64) by omega, pow_add, Nat.mul_div_cancel_left _ (by norm_num),
        Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))]
      simp
    rw [e1, e2, Nat.and_zero, par_zero, Bool.false_xor, and_two_pow, Nat.testBit_div_two_pow,
      show k - 64 + 64 = k by omega]
    by_cases hl : l.testBit k
    · simp [hl, par_two_pow (k - 64) (by omega)]
    · simp [hl, par_zero]

noncomputable section

/-- **`L_c(a)`**: the tree and gate parts of `q_mask − v_mask` at `Δ = e_c` (`c = p_i + b`), as
functions of the mask `a = u_mask` (its `u_low` bits read back by `ZK.maskInv`):
`Σ_{d < k_i} (Σ_{t < k_i} (X^{b+t} mod M_i)_d ⟨maskInv[p_i+t], a⟩) W_tree[p_i+d] +
Σ_{e < 312} G[e]_c ⟨F[e], a⟩ W_gate[e]`. -/
def Lc (c : ℕ) (a : GF128) : GF128 :=
  (∑ d ∈ Finset.range (BAVC.kOf (BAVC.treeOf c)), gf2 (∑ t ∈ Finset.range (BAVC.kOf (BAVC.treeOf c)),
      zb ((pmVal (BAVC.treeOf c) (c - BAVC.bitOffset (BAVC.treeOf c) + t)).testBit d) *
        formHom (ZK.maskInv.getD (BAVC.bitOffset (BAVC.treeOf c) + t) 0) a) *
      natGF (wtL.getD (BAVC.bitOffset (BAVC.treeOf c) + d) 0)) +
    ∑ e ∈ Finset.range 312, gf2 (zb ((trRow CrtGen.G.toList c).testBit e) *
      formHom (CrtGen.F.toList.getD e 0) a) * natGF (trRow CrtGen.wGate.toList e)

lemma Lc_add (c : ℕ) (a b : GF128) : Lc c (a + b) = Lc c a + Lc c b := by
  simp only [Lc, map_add, mul_add, Finset.sum_add_distrib, add_mul]
  ring

/-- `L_c` as an additive map. -/
def LcHom (c : ℕ) : GF128 →+ GF128 := AddMonoidHom.mk' (Lc c) (Lc_add c)

lemma gf2_zb_mul (b : Bool) (x : GF128) : gf2 (zb b) * x = if b then x else 0 := by
  cases b <;> simp

lemma zb_testBit_ite (P : Prop) [Decidable P] (x n : ℕ) :
    zb ((if P then x else 0).testBit n) = if P then zb (x.testBit n) else 0 := by
  split <;> simp

/-- `L_c` on the basis vector `X^k` is what the certificate packs in slot `k`. -/
theorem Lc_basis {c : ℕ} (hc : c < 120) {k : ℕ} (hk : k < 128) :
    Lc c (natGF (2 ^ k)) = natGF (slot (gatePacked c ^^^ treePacked c) k) := by
  rw [slot_xor, natGF_xor, slot_gatePacked c hk, treePacked_eq,
    slot_treePackedAt (tree_bounds hc).1 hk, natGF_xorSum, natGF_xorSum, list_sum_range,
    list_sum_range, Lc, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun e _ => ?_
    rw [formHom_basis _ hk, ← zb_and, gf2_zb_mul, natGF_ite]
  · refine Finset.sum_congr rfl fun d _ => ?_
    rw [natGF_ite, ← gf2_zb_mul, testBit_xorSum, list_sum_range]
    congr 2
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [formHom_basis _ hk, zb_testBit_ite]
    split <;> simp_all [pmVal]

lemma wcL_getD {c : ℕ} (hc : c < 120) : wcL.getD c 0 = trRow CrtGen.wCrt.toList c := by
  rw [List.getD_eq_getElem?_getD, wcL, List.getElem?_map, List.getElem?_range hc]; rfl

/-- **The CRT identity**: for every `c < 120` and every `a`, `L_c(a) = a · W_crt[c]`. -/
theorem Lc_eq {c : ℕ} (hc : c < 120) (a : GF128) :
    Lc c a = a * natGF (wcL.getD c 0) := by
  have hδ : wcL.getD c 0 < 2 ^ 128 := by rw [wcL_getD hc]; exact trRow_lt128 wCrt_size c
  -- The certificate at `c`.
  have hchk : gatePacked c ^^^ treePacked c = rhsPacked (wcL.getD c 0) := by
    have h := crtCheck_eq
    simp only [crtCheck, List.all_eq_true, beq_iff_eq] at h
    have hlen : wcL.length = 120 := by simp [wcL]
    refine h (c, wcL.getD c 0) ?_
    rw [List.mem_iff_getElem]
    refine ⟨c, by simp [hlen, hc], ?_⟩
    rw [List.getElem_zip, List.getElem_range, List.getD_eq_getElem _ _ (by rw [hlen]; exact hc)]
  have hbasis : ∀ k < 128, Lc c (natGF (2 ^ k)) = natGF (2 ^ k) * natGF (wcL.getD c 0) := by
    intro k hk
    rw [Lc_basis hc hk, hchk, slot_rhsPacked hδ hk, natGF_iterate hδ, basis_mul hk]
  conv_lhs => rw [gf_eq_sum a]
  rw [show Lc c (∑ k ∈ Finset.range 128, if (gfNat a).testBit k then natGF (2 ^ k) else 0) =
    LcHom c (∑ k ∈ Finset.range 128, if (gfNat a).testBit k then natGF (2 ^ k) else 0) from rfl,
    map_sum]
  conv_rhs => rw [gf_eq_sum a, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk := Finset.mem_range.1 hk
  split
  · exact hbasis k hk
  · simp

end

end VoleMole.Verifier.Bridge.CrtCheck
