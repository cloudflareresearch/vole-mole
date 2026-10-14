import VoleMole.Arith.UOV
import VoleMole.Arith.GF

/-!
# Claim 2b: pqov's `ov_publicmap` is `UOV.publicMap`

An executable model of pqov's reference public-map evaluation `ov_publicmap` for GF(256)
(`subprojects/pqov/src/ov_publicmap.c:440-463`, with `accu_eval_quad_gf256` at `:169-270` and
`madd_reduce_gf256` at `:381-432`, `UNROLL_4` variant), over an abstract commutative ring `K`, and
the proof that it equals `UOV.publicMap N M pk` (`Arith/UOV.lean`), which is defined by the
`for_each_monomial` layout of `src/uov/public_key.hpp:45-63`. This mechanizes Claim 2b of
`lean/docs/extraction/L7-uov.md` for `ov_publicmap`. (`PublicKey::eval` calls the patched
`ov_publicmap_ct`, patch `pqov-patches/0003`; that function is not modelled here, and its agreement
with `ov_publicmap` stays a test: `ForEachMonomialMatchesPqovLayoutForRandomKeys` in
`tests/uov/test_uov.cpp`, and the dumper checks `ov_publicmap = PublicKey::eval` on its points.)

## Model

`ov_publicmap(y, trimat, x)` reads the expanded key `trimat` once, front to back, one `M`-byte
vector per monomial (`_PUB_M_BYTE = M` for GF(256)):

* P1: `for i < v, for j ∈ [i, v)`, monomial `x_i x_j`;
* P2: `for i < v, for j < o`, monomial `x_i x_{v+j}`;
* P3: `for i ∈ [v, n), for j ∈ [i, n)`, monomial `x_i x_j` (the code splits off `i = n - 1`, which
  differs only in how many padding bytes past the vector it adds; byte `k` of the result only
  depends on byte `k` of each vector, so padding is irrelevant per component).

`visits N M` lists these steps with the running pointer `trimat` (`v = N - M`, `o = N - v`). Each
step computes `idx = x_j · x_i` (`gfv_mul_scalar(_xixj + …, _x[i], …)`) and adds the vector to
bucket `idx & 0xf` of `accu_low` and bucket `idx >> 4` of `accu_high` (`bucketStep`). Then
`madd_reduce_gf256` folds the 16 buckets of each array into four bit planes (`foldPlanes`, the three
`for` loops) and returns `low₁ + low₂·2 + low₄·4 + low₈·8 + high₁·16 + … + high₈·128`
(`maddReduce`).

Over an abstract `K` the nibble split is a pair of functions `lo hi : K → Fin 16`, and the
constants `1, 2, 4, …, 128` are `g : Fin 8 → K`, with the hypotheses `g 0 = 1` and
`c = Σ_b [bit b of lo c] g_b + [bit b of hi c] g_{b+4}` (`IsNibbleSplit`). For `K := GF256` with
`lo c = c & 0xf`, `hi c = c >> 4`, `g = GF256.basis` the latter holds (`GF256.isNibbleSplit`,
by `decide`); the harness runs this instance against the C++.

## Main results

* `visits_eq`: the pointer walk visits P1 rows, P2 rows, P3 rows with `for_each_monomial`'s offsets.
* `ovPublicmap_eq_publicMap` (**Claim 2b**): `ovPublicmap lo hi g N M pk x = publicMap N M pk x`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace VoleMole.Arith.Pqov

open UOV

/-! ## The pointer walk -/

section Walk

/-- One step of an inner loop: visit monomial `x_i x_j` at the current pointer, then
`trimat += vec_len`. -/
def visit (M i : ℕ) (st : List Monomial × ℕ) (j : ℕ) : List Monomial × ℕ :=
  (st.1 ++ [⟨i, j, st.2⟩], st.2 + M)

/-- A doubly nested loop `for i in rows, for j in cols i`, with the running pointer. -/
def loop (M : ℕ) (rows : List ℕ) (cols : ℕ → List ℕ) (st : List Monomial × ℕ) :
    List Monomial × ℕ :=
  rows.foldl (fun st i => (cols i).foldl (visit M i) st) st

/-- The monomials and key offsets read by `accu_eval_quad_gf256`, in order: P1, P2, P3. -/
def visits (N M : ℕ) : List Monomial :=
  let v := N - M
  let o := N - v
  let s1 := loop M (List.range v) (fun i => List.range' i (v - i)) ([], 0)
  let s2 := loop M (List.range v) (fun _ => List.range' v o) s1
  (loop M (List.range' v (N - v)) (fun i => List.range' i (N - i)) s2).1

theorem foldl_visit (M i : ℕ) (L j0 : ℕ) (acc : List Monomial) (p : ℕ) :
    (List.range' j0 L).foldl (visit M i) (acc, p) = (acc ++ row M i j0 (j0 + L) p, p + L * M) := by
  induction L generalizing j0 acc p with
  | zero => simp [row]
  | succ L ih =>
    rw [List.range'_succ, List.foldl_cons, visit, ih]
    simp only [row, Nat.add_sub_cancel_left, List.range_succ_eq_map, List.map_cons, List.map_map,
      List.append_assoc, List.singleton_append, Prod.mk.injEq]
    refine ⟨?_, by ring⟩
    congr 2
    · simp
    · refine List.map_congr_left fun t _ => ?_
      simp only [Function.comp, Monomial.mk.injEq, Nat.succ_eq_add_one]; refine ⟨trivial, ?_, ?_⟩ <;> ring

/-- The outer loop with a closed form `c i` for the pointer at the start of row `i`. -/
theorem loop_range' (M : ℕ) (j0 len c : ℕ → ℕ) (a n : ℕ)
    (hc : ∀ i, a ≤ i → i < a + n → c (i + 1) = c i + len i * M) (acc : List Monomial) :
    loop M (List.range' a n) (fun i => List.range' (j0 i) (len i)) (acc, c a) =
      (acc ++ (List.range' a n).flatMap (fun i => row M i (j0 i) (j0 i + len i) (c i)),
        c (a + n)) := by
  induction n generalizing a acc with
  | zero => simp [loop]
  | succ n ih =>
    simp only [loop] at ih ⊢
    rw [List.range'_succ, List.foldl_cons, foldl_visit, ← hc a le_rfl (by omega),
      ih (a + 1) (fun i h1 h2 => hc i (by omega) (by omega))]
    simp [List.flatMap_cons, Nat.add_right_comm]
    rfl

theorem triangle_succ (n : ℕ) : triangle (n + 1) = triangle n + (n + 1) := by
  simp only [triangle]
  have : (n + 1) * (n + 1 + 1) = n * (n + 1) + (n + 1) * 2 := by ring
  rw [this, Nat.add_mul_div_right _ _ (by norm_num)]

theorem triangle_mono {a b : ℕ} (h : a ≤ b) : triangle a ≤ triangle b :=
  Nat.div_le_div_right (Nat.mul_le_mul h (by omega))

theorem tri_step (M T u : ℕ) (hu : u + 1 ≤ T) :
    M * (triangle T - triangle u) + (u + 1) * M = M * (triangle T - triangle (u + 1)) +
      (u + 1) * M + (u + 1) * M := by
  have h1 := triangle_mono hu
  have h2 := triangle_succ u
  have h3 : triangle u ≤ triangle T := triangle_mono (by omega)
  zify [h1, h3] at *
  rw [h2]; ring

/-- The row pointer step `c (i+1) = c i + (T - i) M` for `c i = p + M (triangle (T - b) -
triangle (T - i))`, `b ≤ i < T`. -/
theorem tri_ptr_step (M T b p i : ℕ) (hb : b ≤ i) (hi : i < T) :
    p + M * (triangle (T - b) - triangle (T - (i + 1))) =
      p + M * (triangle (T - b) - triangle (T - i)) + (T - i) * M := by
  obtain ⟨u, hu⟩ : ∃ u, T - i = u + 1 := ⟨T - i - 1, by omega⟩
  have hu' : T - (i + 1) = u := by omega
  rw [hu, hu']
  have h1 := triangle_mono (show u + 1 ≤ T - b by omega)
  have h2 := triangle_succ u
  have h3 : triangle u ≤ triangle (T - b) := triangle_mono (by omega)
  zify [h1, h3]
  rw [h2]; push_cast; ring

/-- The pointer walk in closed form: the P1 rows, then the P2 rows, then the P3 rows, with
`for_each_monomial`'s offsets (`forEachMonomial` interleaves the P1 and P2 rows). -/
theorem visits_eq (N M : ℕ) :
    visits N M =
      (List.range (N - M)).flatMap (fun i =>
          row M i i (i + (N - M - i)) (M * (triangle (N - M) - triangle (N - M - i)))) ++
        (List.range (N - M)).flatMap (fun i =>
          row M i (N - M) (N - M + (N - (N - M))) (M * triangle (N - M) + i * ((N - (N - M)) * M))) ++
        (List.range' (N - M) (N - (N - M))).flatMap (fun i =>
          row M i i (i + (N - i)) (M * triangle (N - M) + M * (N - M) * M +
            M * (triangle (N - (N - M)) - triangle (N - i)))) := by
  set V := N - M with hV
  have e1 := loop_range' M (fun i => i) (fun i => V - i)
    (fun i => M * (triangle V - triangle (V - i))) 0 V
    (fun i _ hi => by simpa using tri_ptr_step M V 0 0 i (by omega) (by omega)) []
  have e2 := loop_range' M (fun _ => V) (fun _ => N - V)
    (fun i => M * triangle V + i * ((N - V) * M)) 0 V (fun i _ _ => by ring)
    ((List.range' 0 V).flatMap fun i => row M i i (i + (V - i)) (M * (triangle V -
      triangle (V - i))))
  have e3 := loop_range' M (fun i => i) (fun i => N - i)
    (fun i => M * triangle V + M * V * M + M * (triangle (N - V) - triangle (N - i))) V (N - V)
    (fun i h1 h2 => by
      simpa [Nat.add_assoc] using tri_ptr_step M N V (M * triangle V + M * V * M) i h1 (by omega))
    ((List.range' 0 V).flatMap (fun i => row M i i (i + (V - i)) (M * (triangle V -
      triangle (V - i)))) ++ (List.range' 0 V).flatMap fun i =>
        row M i V (V + (N - V)) (M * triangle V + i * ((N - V) * M)))
  have hp : M * triangle V + V * ((N - V) * M) = M * triangle V + M * V * M := by
    rcases Nat.le_total M N with h | h
    · have : N - V = M := by omega
      rw [this]; ring
    · have : V = 0 := by omega
      simp [this]
  have s1 : loop M (List.range' 0 V) (fun i => List.range' i (V - i)) ([], 0) =
      ((List.range' 0 V).flatMap fun i => row M i i (i + (V - i)) (M * (triangle V -
        triangle (V - i))), M * triangle V) := by
    simpa [show triangle 0 = 0 from rfl] using e1
  have s2 := e2
  simp only [Nat.zero_add, zero_mul, add_zero] at s2
  have s3 := e3
  simp only [Nat.sub_self, Nat.mul_zero, add_zero] at s3
  simp only [visits, ← hV, List.range_eq_range', s1, s2, hp, s3]

end Walk

/-! ## Buckets and the reduction -/

section Model

variable {K : Type*}

/-- The bucket arrays `(accu_low, accu_high)`: 16 vectors of `M` bytes each. -/
abbrev Buckets (K : Type*) (M : ℕ) := (Fin 16 → Fin M → K) × (Fin 16 → Fin M → K)

/-- The loop body of `accu_eval_quad_gf256`: with `idx = x_j · x_i`, add the key vector at the
current pointer to `accu_low[idx & 0xf]` and to `accu_high[idx >> 4]`. -/
def bucketStep [Add K] [Mul K] (lo hi : K → Fin 16) {M : ℕ} (pk : ℕ → K) (x : ℕ → K)
    (b : Buckets K M) (m : Monomial) : Buckets K M :=
  let idx := x m.j * x m.i
  let vec : Fin M → K := fun k => pk (m.off + k)
  (Function.update b.1 (lo idx) (b.1 (lo idx) + vec),
    Function.update b.2 (hi idx) (b.2 (hi idx) + vec))

/-- `t[d] += t[s]` (`gf256v_add(tmp + TMPVEC_LEN * d, tmp + TMPVEC_LEN * s, …)`). -/
def addInto {V : Type*} [Add V] (t : Fin 16 → V) (d s : Fin 16) : Fin 16 → V :=
  Function.update t d (t d + t s)

/-- The three folding loops of `madd_reduce_gf256` (`ov_publicmap.c:394-405`):
`for i = 15..9: t[8] += t[i], t[i-8] += t[i]`; `for i = 7..5: t[4] += t[i], t[i-4] += t[i]`;
`for i = 3: t[2] += t[i], t[i-2] += t[i]`. Afterwards `t[2^b]` is the sum of the buckets whose
index has bit `b` set (`foldPlanes_one` … `foldPlanes_eight`). -/
def foldPlanes {V : Type*} [Add V] (t : Fin 16 → V) : Fin 16 → V :=
  let t := ([15, 14, 13, 12, 11, 10, 9] : List (Fin 16)).foldl
    (fun t i => addInto (addInto t 8 i) (i - 8) i) t
  let t := ([7, 6, 5] : List (Fin 16)).foldl (fun t i => addInto (addInto t 4 i) (i - 4) i) t
  ([3] : List (Fin 16)).foldl (fun t i => addInto (addInto t 2 i) (i - 2) i) t

/-- `madd_reduce_gf256` (`ov_publicmap.c:381-432`) on component `k`: fold both bucket arrays, then
`y = low[1] + low[2]·2 + low[4]·4 + low[8]·8 + high[1]·16 + high[2]·32 + high[4]·64 +
high[8]·128`, with the constants `2^b` given as `g b` (`gf256v_madd(y, a, c)` is `y += a · c`). -/
def maddReduce [Add K] [Mul K] [Zero K] {M : ℕ} (g : Fin 8 → K) (b : Buckets K M) : Fin M → K :=
  let tl := foldPlanes b.1
  let th := foldPlanes b.2
  fun k => 0 + tl 1 k + tl 2 k * g 1 + tl 4 k * g 2 + tl 8 k * g 3 + th 1 k * g 4 + th 2 k * g 5 +
    th 4 k * g 6 + th 8 k * g 7

/-- **pqov's `ov_publicmap`** (`ov_publicmap.c:440-463`, GF(256) branch): `_x[i] = x[i]`, the
bucket accumulation `accu_eval_quad_gf256` over the key `pk` (`trimat`), then `madd_reduce_gf256`.
`lo`, `hi` are the nibble split `idx & 0xf`, `idx >> 4`, and `g b = 2^b` as a field element. -/
def ovPublicmap [Add K] [Mul K] [Zero K] (lo hi : K → Fin 16) (g : Fin 8 → K) (N M : ℕ)
    (pk : ℕ → K) (x : ℕ → K) : Fin M → K :=
  maddReduce g ((visits N M).foldl (bucketStep lo hi pk x) (fun _ _ => 0, fun _ _ => 0))

/-- The value of a byte given its nibbles: `Σ_b [bit b of lo] g_b + [bit b of hi] g_{b+4}`. -/
def nibbleVal [Add K] [Zero K] (g : Fin 8 → K) (lo hi : Fin 16) : K :=
  let sel (a : Fin 16) (b : ℕ) (c : K) : K := if a.val.testBit b then c else 0
  sel lo 0 (g 0) + sel lo 1 (g 1) + sel lo 2 (g 2) + sel lo 3 (g 3) + sel hi 0 (g 4) +
    sel hi 1 (g 5) + sel hi 2 (g 6) + sel hi 3 (g 7)

/-- The hypotheses on the nibble split: `g 0 = 1`, and every `c` is the value of its nibbles. -/
structure IsNibbleSplit [Add K] [Zero K] [One K] (lo hi : K → Fin 16) (g : Fin 8 → K) : Prop where
  g_zero : g 0 = 1
  split : ∀ c, c = nibbleVal g (lo c) (hi c)

end Model

/-! ## Correctness -/

section Correct

variable {K : Type*} [CommRing K]

theorem foldPlanes_apply {V : Type*} [AddCommMonoid V] (t : Fin 16 → V) :
    foldPlanes t 1 = ∑ a : Fin 16, (if a.val.testBit 0 then t a else 0) ∧
    foldPlanes t 2 = ∑ a : Fin 16, (if a.val.testBit 1 then t a else 0) ∧
    foldPlanes t 4 = ∑ a : Fin 16, (if a.val.testBit 2 then t a else 0) ∧
    foldPlanes t 8 = ∑ a : Fin 16, (if a.val.testBit 3 then t a else 0) := by
  simp only [foldPlanes, addInto, List.foldl_cons, List.foldl_nil, Function.update_apply,
    Fin.sum_univ_succ, Fin.sum_univ_zero]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp (config := { decide := true }) <;> abel

theorem foldl_bucketStep (lo hi : K → Fin 16) {M : ℕ} (pk : ℕ → K) (x : ℕ → K)
    (L : List Monomial) (b : Buckets K M) (a : Fin 16) (k : Fin M) :
    (L.foldl (bucketStep lo hi pk x) b).1 a k =
        b.1 a k + (L.map fun m => if a = lo (x m.j * x m.i) then pk (m.off + k) else 0).sum ∧
      (L.foldl (bucketStep lo hi pk x) b).2 a k =
        b.2 a k + (L.map fun m => if a = hi (x m.j * x m.i) then pk (m.off + k) else 0).sum := by
  induction L generalizing b with
  | nil => simp
  | cons m L ih =>
    rw [List.foldl_cons, (ih _).1, (ih _).2]
    simp only [bucketStep, Function.update_apply, List.map_cons, List.sum_cons]
    constructor <;> split_ifs with h <;> simp [h, add_assoc]

/-- Summing a bit plane of the buckets: the buckets whose index has bit `c` set. -/
theorem sum_plane (f : Monomial → Fin 16) (p : Monomial → K) (c : ℕ) (L : List Monomial) :
    ∑ a : Fin 16, (if a.val.testBit c then
        (L.map fun m => if a = f m then p m else 0).sum else 0) =
      (L.map fun m => if (f m).val.testBit c then p m else 0).sum := by
  induction L with
  | nil => simp
  | cons m L ih =>
    simp only [List.map_cons, List.sum_cons, ite_add_zero, Finset.sum_add_distrib, ih]
    congr 1
    rw [Finset.sum_eq_single (f m) (fun a _ ha => by simp [ha]) (by simp)]
    simp

theorem head_eq (g : Fin 8 → K) (hg0 : g 0 = 1) (lo hi : Fin 16) (p : K) :
    0 + (if lo.val.testBit 0 then p else 0) + (if lo.val.testBit 1 then p else 0) * g 1 +
      (if lo.val.testBit 2 then p else 0) * g 2 + (if lo.val.testBit 3 then p else 0) * g 3 +
      (if hi.val.testBit 0 then p else 0) * g 4 + (if hi.val.testBit 1 then p else 0) * g 5 +
      (if hi.val.testBit 2 then p else 0) * g 6 + (if hi.val.testBit 3 then p else 0) * g 7 =
    p * nibbleVal g lo hi := by
  simp only [nibbleVal, ite_mul, zero_mul, mul_add, mul_ite, mul_zero, hg0, mul_one, zero_add]

/-- The reduction of the bit-plane sums of any visit list is `Σ_m p_m c_m`. -/
theorem reduce_eq (lo hi : K → Fin 16) (g : Fin 8 → K) (hs : IsNibbleSplit lo hi g)
    (c p : Monomial → K) (L : List Monomial) :
    let S (f : K → Fin 16) (b : ℕ) := (L.map fun m => if (f (c m)).val.testBit b then p m else 0).sum
    0 + S lo 0 + S lo 1 * g 1 + S lo 2 * g 2 + S lo 3 * g 3 + S hi 0 * g 4 + S hi 1 * g 5 +
      S hi 2 * g 6 + S hi 3 * g 7 = (L.map fun m => p m * c m).sum := by
  induction L with
  | nil => simp
  | cons m L ih =>
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    have h := head_eq g hs.g_zero (lo (c m)) (hi (c m)) (p m)
    rw [← hs.split (c m)] at h
    linear_combination ih + h

theorem sum_flatMap {α : Type*} (f : ℕ → List α) (φ : α → K) (L : List ℕ) :
    ((L.flatMap f).map φ).sum = (L.map fun a => ((f a).map φ).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, ih]

/-- The pointer walk and `for_each_monomial` visit the same monomials with the same offsets (in a
different order), so sums over them agree. -/
theorem sum_visits (N M : ℕ) (φ : Monomial → K) :
    ((visits N M).map φ).sum = ((forEachMonomial N M).map φ).sum := by
  rw [visits_eq, forEachMonomial]
  simp only [List.map_append, List.sum_append, sum_flatMap, List.sum_map_add, add_assoc]
  congr 1
  · refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
    rw [List.mem_range] at hi
    rw [Nat.add_sub_cancel' hi.le]
  congr 1
  · refine congrArg List.sum (List.map_congr_left fun i _ => ?_)
    rw [Nat.add_sub_cancel' (Nat.sub_le N M)]
  · refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
    rw [List.mem_range'_1] at hi
    rw [Nat.add_sub_cancel' (by omega : i ≤ N)]

/-- **Claim 2b.** pqov's reference `ov_publicmap` computes `UOV.publicMap`, the public map read
with `for_each_monomial`'s layout, for every key `pk` and input `x`. -/
theorem ovPublicmap_eq_publicMap (lo hi : K → Fin 16) (g : Fin 8 → K)
    (hs : IsNibbleSplit lo hi g) (N M : ℕ) (pk : ℕ → K) (x : ℕ → K) :
    ovPublicmap lo hi g N M pk x = publicMap N M pk x := by
  funext k
  have hplane (f : Fin 16 → Fin M → K) (b : ℕ) (a : Fin 16) :
      (if a.val.testBit b then f a else 0) k = if a.val.testBit b then f a k else 0 := by
    split_ifs <;> rfl
  obtain ⟨l1, l2, l4, l8⟩ := foldPlanes_apply
    ((visits N M).foldl (bucketStep lo hi pk x) (fun _ _ => 0, fun _ _ => 0)).1
  obtain ⟨h1, h2, h4, h8⟩ := foldPlanes_apply
    ((visits N M).foldl (bucketStep lo hi pk x) (fun _ _ => 0, fun _ _ => 0)).2
  simp only [ovPublicmap, maddReduce]
  rw [l1, l2, l4, l8, h1, h2, h4, h8]
  simp only [Finset.sum_apply, hplane,
    (foldl_bucketStep lo hi pk x _ _ _ k).1, (foldl_bucketStep lo hi pk x _ _ _ k).2, zero_add,
    sum_plane]
  have := reduce_eq lo hi g hs (fun m => x m.j * x m.i) (fun m => pk (m.off + k)) (visits N M)
  simp only [zero_add] at this
  rw [this, sum_visits, publicMap]
  exact congrArg List.sum (List.map_congr_left fun m _ => by ring)

end Correct

/-! ## The concrete instance `K := GF256` -/

namespace GF256

/-- `idx & 0xf`. -/
def lo (c : GF256) : Fin 16 := ⟨c.val.toNat % 16, Nat.mod_lt _ (by norm_num)⟩

/-- `idx >> 4`. -/
def hi (c : GF256) : Fin 16 := ⟨c.val.toNat / 16, by have := c.val.toNat_lt; omega⟩

theorem split_all : ∀ n : Fin 256,
    (⟨n.val.toUInt8⟩ : GF256) = nibbleVal GF256.basis (lo ⟨n.val.toUInt8⟩) (hi ⟨n.val.toUInt8⟩) := by
  decide +kernel

/-- The nibble split of pqov's GF(256) (`g = GF256.basis`, `g b = 2^b`) satisfies `IsNibbleSplit`.
(`GF256` has no `CommRing` instance, so `ovPublicmap_eq_publicMap` does not apply to it directly;
`lake exe arith_vectors` runs `ovPublicmap GF256.lo GF256.hi GF256.basis` against pqov.) -/
theorem isNibbleSplit : IsNibbleSplit lo hi GF256.basis where
  g_zero := rfl
  split c := by
    have := split_all ⟨c.val.toNat, c.val.toNat_lt⟩
    have e : (⟨c.val.toNat.toUInt8⟩ : VoleMole.Arith.GF256) = c := GF256.ext' UInt8.ofNat_toNat
    simpa only [e] using this

end GF256

end VoleMole.Arith.Pqov
