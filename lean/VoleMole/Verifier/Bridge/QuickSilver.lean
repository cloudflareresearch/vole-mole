import VoleMole.Verifier.Bridge.Field
import VoleMole.EndToEnd.Core

/-!
# Bridge: the executable QuickSilver check is `EndToEnd.qsCheck` plus `Seed.maskPoly`

`EndToEnd/Core.lean` states the accepting condition of the extraction argument on what the
verifier computes: `EndToEnd.qsCheck cs d χ m Δ + R(Δ) = 0`, where `qsCheck` evaluates the degree-tracking
circuits `sysQS cs d` (`toQS`, with the degree raisings the C++ types insert) on the witness MACs
`m` and combines them with the ZKHash weights `χ`, and `R = Seed.maskPoly d a b ã z` collects the
masks, the prover's `ã` and the prover's check value `z`. The executable verifier
(`Verifier/QuickSilver.lean`) instead evaluates each constraint once, at `x_j = q_j·Δ⁻¹`, and
multiplies by `Δ^d`, and computes the mask term with a loop over `q_mask` and `ã`.

## The degree bookkeeping (model only, no `GF128`)

* `mac_toQS`: for `Δ ≠ 0`, the verifier's MAC of `toQS e` is `Δ^{deg e} · e(m/Δ)`;
* `mac_constraintQS`: hence for `deg e ≤ d`, the MAC of `constraintQS d e` (`add_constraint`) is
  `Δ^d · e(m/Δ)`. This is the argument the comment of `Verifier/QuickSilver.lean` gives for
  skipping the degree bookkeeping, now proved;
* `qsCheck_zkCoeff`: with the ZKHash weights of `chall₂ = (r₀, r₁, s, t)`, `qsCheck` is
  `r₀·horner_s(c) + r₁·horner_t(c)` with `c_k = Δ^d · f_k(m/Δ)`, the two hashes the code computes
  (`Seed.zkHash`).

## The executable check (for any field embedding `φ`)

* `map_constraintKeys`: `φ` of the executable constraint values is `c_k` above, at
  `m_j = φ(key_j)` and `Δ = φ(Δ_lifted)`, if the relation's `GF128` evaluator is the system `cs`
  transported along `φ` (`hvals`; see below) and `F` has `2¹²⁸` elements (for `gfInv`);
* `map_qsCheck`: `φ(check_V) + z = EndToEnd.qsCheck cs d (zkCoeff …) m Δ + (maskPoly d a b ã z).eval Δ`,
  whenever the constraint values are those MACs and each mask MAC `φ q_mask[i]` (`i < d − 1`) is
  `a_i + b_i·Δ`; `ã_i = φ ã_{i−1}` (the proof's `ã`, indexed from 1 in the model);
* `hacc_of_qsCheck`: in characteristic 2, with `z := φ(check_V)` (the value the verifier hashes into
  `chal3`), the accepting equation of `EndToEnd.claim3_of_system` / `extract_or_few` holds.

**Assumed:** besides the embedding (`Bridge/Field.lean`), `hvals` — that the relation's evaluator
`values : (ℕ → GF128) → List GF128` (the `Arith/*` sharing evaluators at `F := GF128`) commutes
with `φ`, i.e. maps to `System.values cs` over `F`. The evaluators are generic in the field, and
the `Arith/*` files prove them equal to `System.values` (e.g. `issueValues_eq`), so this is
parametricity; `eval_map` below does the `System` half.
-/

open Finset Polynomial

namespace VoleMole.Verifier.Bridge

open VoleMole.Arith VoleMole.Verifier VoleMole.EndToEnd VoleMole.EndToEnd.QSExprMac

/-! ## The degree bookkeeping -/

section Model

variable {F : Type*} [Field F]

/-- The verifier's MAC of a translated expression is `Δ^{deg e} · e(m/Δ)`. -/
theorem mac_toQS (m : ℕ → F) {Δ : F} (hΔ : Δ ≠ 0) :
    ∀ e : Expr F, mac m Δ (toQS e) = Δ ^ e.degree * e.eval (fun j => m j * Δ⁻¹)
  | .wit j => by simp [toQS, mac, Expr.degree, Expr.eval]; field_simp
  | .const c => by simp [toQS, mac, Expr.degree, Expr.eval]
  | .add a b => by
      simp only [toQS, mac, mac_toQS m hΔ a, mac_toQS m hΔ b, Expr.degree, Expr.eval]
      rw [mul_assoc, mul_comm (Expr.eval _ a), ← mul_assoc, ← pow_add, mul_assoc,
        mul_comm (Expr.eval _ b), ← mul_assoc, ← pow_add, Nat.add_sub_cancel' (le_max_left _ _),
        Nat.add_sub_cancel' (le_max_right _ _), mul_add]
  | .mul a b => by
      simp only [toQS, mac, mac_toQS m hΔ a, mac_toQS m hΔ b, Expr.degree, Expr.eval, pow_add]
      ring

/-- **The verifier's constraint MAC is `Δ^d · f(m/Δ)`.** -/
theorem mac_constraintQS (m : ℕ → F) {Δ : F} (hΔ : Δ ≠ 0) {d : ℕ} (e : Expr F)
    (he : e.degree ≤ d) :
    mac m Δ (constraintQS d e) = Δ ^ d * e.eval (fun j => m j * Δ⁻¹) := by
  rw [constraintQS, mac, mac_toQS m hΔ, mul_comm, ← mul_assoc, ← pow_add,
    Nat.sub_add_cancel he]

/-- The constraint values the executable verifier hashes: `c_k = Δ^d · f_k(m/Δ)`. -/
def keyVals (cs : System F) (d : ℕ) (m : ℕ → F) (Δ : F) : Fin cs.length → F :=
  fun k => Δ ^ d * (cs.get k).eval (fun j => m j * Δ⁻¹)

/-- **`EndToEnd.qsCheck` with the ZKHash weights is the code's ZKHash of the `c_k`.** -/
theorem qsCheck_zkCoeff (cs : System F) {d : ℕ} (hdeg : ∀ e ∈ cs, e.degree ≤ d) (m : ℕ → F)
    {Δ : F} (hΔ : Δ ≠ 0) (r₀ r₁ s t : F) :
    EndToEnd.qsCheck cs d (Seed.zkCoeff cs.length r₀ r₁ s t) m Δ =
      r₀ * Seed.horner s cs.length (keyVals cs d m Δ) +
        r₁ * Seed.horner t cs.length (keyVals cs d m Δ) := by
  rw [← Seed.zkHash, Seed.zkHash_eq_sum, EndToEnd.qsCheck]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sysQS, mac_constraintQS m hΔ _ (hdeg _ (List.get_mem cs k)), keyVals]

end Model

/-! ## The executable check -/

variable {F : Type*} [Field F] (φ : GFEmbedding F)

/-- An expression over `GF128`, mapped along `φ`, evaluates to `φ` of its value. -/
theorem eval_map (w : ℕ → GF128) : ∀ e : Expr GF128, (e.map φ).eval (φ ∘ w) = φ (e.eval w)
  | .wit _ => rfl
  | .const _ => rfl
  | .add a b => by simp [Expr.map, Expr.eval, eval_map w a, eval_map w b]
  | .mul a b => by simp [Expr.map, Expr.eval, eval_map w a, eval_map w b]

lemma map_foldl_add (l : List GF128) (init : GF128) :
    φ (l.foldl (· + ·) init) = φ init + (l.map φ).sum := by
  induction l generalizing init with
  | nil => simp
  | cons x l ih => simp [ih, add_assoc]

/-- **The executable constraint values.** If the relation's evaluator is `cs` transported along `φ`
(`hvals`), `φ` of `constraintKeys` is the list of `c_k = Δ^d · f_k(m/Δ)` at `m_j = φ(key_j)`,
`Δ = φ(Δ_lifted)`. -/
theorem map_constraintKeys [Fintype F] (hF : Fintype.card F = 2 ^ 128) (p : Params)
    (keys : Array GF128) (deltaL : GF128) (values : (ℕ → GF128) → List GF128) (cs : System F)
    (hvals : ∀ x, (values x).map φ = cs.values (φ ∘ x)) :
    (constraintKeys p keys deltaL values).map φ =
      List.ofFn (keyVals cs p.qsDegree (fun j => φ (keys.getD j 0)) (φ deltaL)) := by
  simp only [constraintKeys, List.map_map]
  have h1 : (φ ∘ fun x => gfPow deltaL p.qsDegree * x) =
      (fun y => φ deltaL ^ p.qsDegree * y) ∘ φ := by
    funext x; simp [φ.map_gfPow]
  rw [h1, ← List.map_map, hvals]
  have h2 : (φ ∘ fun j => (keys.map (· * gfInv deltaL)).getD j 0) =
      fun j => φ (keys.getD j 0) * (φ deltaL)⁻¹ := by
    funext j
    simp only [Function.comp, Array.getD_eq_getD_getElem?, Array.getElem?_map]
    cases keys[j]? <;> simp [φ.map_gfInv hF]
  rw [h2, System.values, List.map_map]
  apply List.ext_get (by simp)
  intro k h1 h2
  simp [keyVals]

/-- The mask term of `Verifier.qsCheck`. -/
lemma map_mask (d : ℕ) (hd : 2 ≤ d) (aT : ℕ → GF128) (qm : ℕ → GF128) (deltaL : GF128) :
    φ (((List.range (d - 2)).map fun j => (aT j + qm (j + 1)) * gfPow deltaL (j + 1)).foldl
        (· + ·) (qm 0) + aT (d - 2) * gfPow deltaL (d - 1)) =
      ∑ i ∈ range (d - 1), φ (qm i) * φ deltaL ^ i +
        ∑ i ∈ Ico 1 d, φ (aT (i - 1)) * φ deltaL ^ i := by
  rw [φ.map_add', map_foldl_add, List.map_map, φ.map_mul', φ.map_gfPow]
  have hsum : ((List.range (d - 2)).map (φ ∘ fun j => (aT j + qm (j + 1)) * gfPow deltaL (j + 1))).sum =
      ∑ j ∈ range (d - 2), (φ (aT j) + φ (qm (j + 1))) * φ deltaL ^ (j + 1) := by
    rw [← List.sum_toFinset _ (List.nodup_range), List.toFinset_range]
    · exact Finset.sum_congr rfl fun j _ => by simp [φ.map_gfPow]
  rw [hsum]
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 2 := ⟨d - 2, by omega⟩
  simp only [show n + 2 - 2 = n by omega, show n + 2 - 1 = n + 1 by omega]
  rw [Finset.sum_range_succ', Finset.sum_Ico_eq_sum_range, show n + 2 - 1 = n + 1 by omega,
    Finset.sum_range_succ]
  simp only [add_mul, Finset.sum_add_distrib, pow_zero, mul_one, add_comm 1, Nat.add_sub_cancel]
  ring

/-- **The executable QuickSilver check value.** If the constraint values `cs` are the MACs of the
system's circuits at `m`, `Δ = φ(Δ_lifted)` (`hcs`, from `map_constraintKeys` and
`mac_constraintQS`), and each mask MAC `φ q_mask[i]`, `i < d − 1`, is `a_i + b_i·Δ`, then
`φ(check_V) + z` is `EndToEnd.qsCheck` with the ZKHash weights of `chal2` plus the model's
remainder `maskPoly d a b ã z` at `Δ`, for every `z`. -/
theorem map_qsCheck (pf : Proof) (chal2 : ByteArray) (csV : List GF128) (qMask : Array W128)
    (deltaL : GF128) (cs : System F) (m : ℕ → F)
    (hcs : csV.map φ = List.ofFn fun k => mac m (φ deltaL) (sysQS cs pf.params.qsDegree k))
    (a b : ℕ → F) (hmask : ∀ i < pf.params.qsDegree - 1,
      φ qMask[i]!.toGF = a i + b i * φ deltaL) (z : F) :
    φ (Verifier.qsCheck pf chal2 csV qMask deltaL) + z =
      EndToEnd.qsCheck cs pf.params.qsDegree
          (Seed.zkCoeff cs.length (φ (gfOfBytes chal2 0)) (φ (gfOfBytes chal2 16))
            (φ (gfOfBytes chal2 32)) (φ ⟨W128.word chal2 48, 0⟩)) m (φ deltaL) +
        (Seed.maskPoly pf.params.qsDegree a b
          (fun i => φ (gfOfBytes pf.qsProof (16 * (i - 1)))) z).eval (φ deltaL) := by
  have hlen : csV.length = cs.length := by simpa using congrArg List.length hcs
  simp only [Verifier.qsCheck, φ.map_add', φ.map_mul']
  generalize pf.params.qsDegree = d at *
  -- The ZKHash part.
  have hzk : ∀ key : GF128, φ (horner key csV.toArray) =
      Seed.horner (φ key) cs.length fun k => mac m (φ deltaL) (sysQS cs d k) := by
    intro key
    rw [φ.map_horner, Seed.horner_eq_sum, Seed.horner_eq_sum]
    refine Fintype.sum_equiv (finCongr (by simp [hlen])) _ _ fun k => ?_
    have hk : (k : ℕ) < csV.length := by simpa using k.isLt
    have hk' : (k : ℕ) < cs.length := hlen ▸ hk
    have := congrArg (fun l => l[(k : ℕ)]?) hcs
    simp [List.getElem?_eq_getElem hk, hk'] at this
    simp only [finCongr_apply, Fin.val_cast, List.size_toArray, hlen, Fin.getElem_fin,
      List.getElem_toArray, this]
    rfl
  have hqs : EndToEnd.qsCheck cs d (Seed.zkCoeff cs.length (φ (gfOfBytes chal2 0))
      (φ (gfOfBytes chal2 16)) (φ (gfOfBytes chal2 32)) (φ ⟨W128.word chal2 48, 0⟩)) m
      (φ deltaL) =
      φ (gfOfBytes chal2 0) * φ (horner (gfOfBytes chal2 32) csV.toArray) +
        φ (gfOfBytes chal2 16) * φ (horner ⟨W128.word chal2 48, 0⟩ csV.toArray) := by
    rw [hzk, hzk, ← Seed.zkHash, Seed.zkHash_eq_sum, EndToEnd.qsCheck]
  rw [hqs]
  -- The mask part.
  simp only [Seed.maskPoly, eval_add, eval_finsetSum, eval_mul, eval_C, eval_X, eval_pow]
  by_cases hd : 2 ≤ d
  · have hM := map_mask φ d hd (fun i => gfOfBytes pf.qsProof (16 * i)) (fun i => qMask[i]!.toGF)
      deltaL
    simp only [hd, ↓reduceIte]
    rw [hM]
    have hm : ∑ i ∈ range (d - 1), φ qMask[i]!.toGF * φ deltaL ^ i =
        ∑ i ∈ range (d - 1), (a i + b i * φ deltaL) * φ deltaL ^ i :=
      Finset.sum_congr rfl fun i hi => by rw [hmask i (Finset.mem_range.1 hi)]
    rw [hm]
    ring
  · simp only [hd, ↓reduceIte]
    have h1 : d - 1 = 0 := by omega
    have h2 : Ico 1 d = ∅ := Finset.Ico_eq_empty (by omega)
    simp [h1, h2]

/-- **The accepting equation of `EndToEnd`.** In characteristic 2, with `z = φ(check_V)`, the value
the verifier hashes into `chal3`, the equation `qsCheck + R(Δ) = 0` that
`EndToEnd.claim3_of_system` and `extract_or_few` assume on the accepting set holds at this
transcript's `Δ`. -/
theorem hacc_of_qsCheck [CharP F 2] (pf : Proof) (chal2 : ByteArray) (csV : List GF128)
    (qMask : Array W128) (deltaL : GF128) (cs : System F) (m : ℕ → F)
    (hcs : csV.map φ = List.ofFn fun k => mac m (φ deltaL) (sysQS cs pf.params.qsDegree k))
    (a b : ℕ → F) (hmask : ∀ i < pf.params.qsDegree - 1,
      φ qMask[i]!.toGF = a i + b i * φ deltaL) :
    EndToEnd.qsCheck cs pf.params.qsDegree
        (Seed.zkCoeff cs.length (φ (gfOfBytes chal2 0)) (φ (gfOfBytes chal2 16))
          (φ (gfOfBytes chal2 32)) (φ ⟨W128.word chal2 48, 0⟩)) m (φ deltaL) +
      (Seed.maskPoly pf.params.qsDegree a b (fun i => φ (gfOfBytes pf.qsProof (16 * (i - 1))))
        (φ (Verifier.qsCheck pf chal2 csV qMask deltaL))).eval (φ deltaL) = 0 := by
  rw [← map_qsCheck φ pf chal2 csV qMask deltaL cs m hcs a b hmask, CharTwo.add_self_eq_zero]

end VoleMole.Verifier.Bridge
