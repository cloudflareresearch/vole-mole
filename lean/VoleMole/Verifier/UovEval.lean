import VoleMole.Arith.GF
import VoleMole.Arith.Moussaka
import VoleMole.Arith.Ratatouille
import VoleMole.Arith.PomFRIT

/-!
# Fast evaluation of the UOV constraints over `GF128` (executable, proved equal)

The `Arith/*` generators build each UOV constraint as an `Expr` tree
(`UOV.evalCombinedPublicMap`): one node per monomial, whose constant is `combineVec β toBits l
(p_m)` = `Σ_k l_k ι(p^k_m)`, i.e. 45 · 9 field multiplications per monomial (`ι` by `embed`), and
whose variables `s_j = byteLoad β (o + j)` are re-evaluated (8 more multiplications) at every
monomial. Walking those trees cost ≈ 2.3 s per public key. Here the same values are computed
directly:

* `publicMapValue`: the loop of `qs_eval_combined_public_map` (`UOV.evalStep`,
  `circuit.hpp:127-133`) run on field values instead of expressions
  (`eval_evalCombinedPublicMap`, for any `+`, `*`);
* `combTab l`: the table `l_k · ι(a)` for all `k < M` and bytes `a` (as `Combination`'s tables in
  the C++, `circuit.hpp:79-105`), so a monomial's coefficient is `M` lookups (`coeff_combTab`);
* `byteVals`: the `N` loaded variables `s_j`, computed once per proof and shared by all keys
  (`loadFn_byteVals`).

`publicMapFast_eq` combines them: `publicMapFast` is the `Expr.eval` of the generator's
expression. The relation evaluators `moussakaRedeemValues`, `ratatouilleSpendValues` and
`pomfritRedeemValues` replace only the UOV term of `Moussaka.redeemValues`,
`Ratatouille.spendValues` and `System.values (PomFRIT.pomfritRedeemSystem …)` and are proved
equal to them (`moussakaRedeemValues_eq`, `ratatouilleSpendValues_eq`, `pomfritRedeemValues_eq`),
so the bridge theorems (`Bridge/Relations.lean`) are about the code that runs.
-/

namespace VoleMole.Verifier

open VoleMole.Arith VoleMole.Arith.UOV

/-- An array as a function on `Fin n`. Apply it to an already computed array: a definition of the
form `def f x : α → β := let a := …; fun y => …` is compiled with arity 2, so `a` would be
recomputed at every application. -/
def ofArr {n : ℕ} (a : Array GF128) : Fin n → GF128 := fun k => a.getD k.val 0

/-- `beta` tabulated once (`beta b` decodes a byte list at every call). -/
def betaTab : Array GF128 := (Array.range 8).map fun b => if h : b < 8 then beta ⟨b, h⟩ else 0

/-- `beta`, by table lookup. -/
def betaFast (b : Fin 8) : GF128 := betaTab.getD b.val 0

namespace UovEval

/-! ## The gadget's loop on values -/

section Generic

variable {F K : Type*} [Add F] [Mul F]

/-- `UOV.evalStep` on values: the state is `(y, row, current_i)`. -/
def evalStepV (c : Monomial → F) (x : ℕ → F) (zero1 : F) (st : F × F × ℕ) (m : Monomial) :
    F × F × ℕ :=
  if m.i = st.2.2 then (st.1, st.2.1 + c m * x m.j, st.2.2)
  else (st.1 + x st.2.2 * st.2.1, zero1 + c m * x m.j, m.i)

/-- `qs_eval_combined_public_map` on values, with the monomial coefficients `c`. -/
def publicMapValue (c : Monomial → F) (N M : ℕ) (x : ℕ → F) : F :=
  let zero1 := x 0 + x 0
  let st := (forEachMonomial N M).foldl (evalStepV c x zero1) (zero1 * zero1, zero1, 0)
  st.1 + x st.2.2 * st.2.1

theorem foldl_evalStep_eval (c : Monomial → F) (s : ℕ → Expr F) (zero1 : Expr F) (w : ℕ → F)
    (L : List Monomial) (st : EvalState F) :
    let st' := L.foldl (evalStep c s zero1) st
    (st'.1.eval w, st'.2.1.eval w, st'.2.2) =
      L.foldl (evalStepV c (fun i => (s i).eval w) (zero1.eval w))
        (st.1.eval w, st.2.1.eval w, st.2.2) := by
  induction L generalizing st with
  | nil => rfl
  | cons m L ih =>
    simp only [List.foldl_cons]
    rw [ih]
    congr 1
    unfold evalStep evalStepV
    split_ifs <;> rfl

/-- The generator's expression evaluates to `publicMapValue` of the evaluated variables. -/
theorem eval_evalCombinedPublicMap [Zero F] [One F] (β : Fin 8 → F) (toBits : K → Fin 8 → Bool)
    (N M : ℕ) (pk : ℕ → K) (s : ℕ → Expr F) (l : Fin M → F) (w : ℕ → F) :
    (evalCombinedPublicMap β toBits N M pk s l).eval w =
      publicMapValue (fun m => combineVec β toBits l fun k => pk (m.off + k)) N M
        (fun i => (s i).eval w) := by
  have h := foldl_evalStep_eval (fun m => combineVec β toBits l fun k => pk (m.off + k)) s
    (s 0 + s 0) w (forEachMonomial N M) ((s 0 + s 0) * (s 0 + s 0), s 0 + s 0, 0)
  simp only [Expr.eval_add, Expr.eval_mul] at h
  simp only [evalCombinedPublicMap, publicMapValue, Expr.eval_add, Expr.eval_mul, ← h]

/-- `Σ_u f_u` accumulated as `acc = a; acc += f_u`, evaluated. -/
theorem eval_foldl_add {α : Type*} (f : α → Expr F) (L : List α) (a : Expr F) (w : ℕ → F) :
    (L.foldl (fun acc u => acc + f u) a).eval w =
      L.foldl (fun acc u => acc + (f u).eval w) (a.eval w) := by
  induction L generalizing a with
  | nil => rfl
  | cons u L ih => exact ih _

end Generic

/-! ## Tables over `GF128` -/

/-- `ι(a) = embed β (bits of a)` for all 256 bytes. -/
def iotaTab : Array GF128 :=
  (Array.range 256).map fun v => embed betaFast (GF256.toBits ⟨v.toUInt8⟩)

/-- `l_k · ι(a)` at index `256 k + a`, for `k < M`. -/
def combTab (M : ℕ) (l : Array GF128) : Array GF128 :=
  (Array.range (256 * M)).map fun i => l.getD (i / 256) 0 * iotaTab.getD (i % 256) 0

/-- The coefficient `Σ_k l_k ι(pk(off + k))` of the monomial at offset `off`, from `combTab`. -/
def coeff (tab : Array GF128) (M : ℕ) (pk : ℕ → GF256) (off : ℕ) : GF128 :=
  Fin.foldl M (fun acc k => acc + tab.getD (256 * k.val + (pk (off + k.val)).val.toNat) 0) 0

theorem combTab_getD (M : ℕ) (l : Array GF128) (k : Fin M) (a : GF256) :
    (combTab M l).getD (256 * k.val + a.val.toNat) 0 =
      ofArr (n := M) l k * embed betaFast (GF256.toBits a) := by
  have ha : a.val.toNat < 256 := a.val.toNat_lt
  have hk := k.isLt
  have hi : 256 * k.val + a.val.toNat < 256 * M := by omega
  have hdiv : (256 * k.val + a.val.toNat) / 256 = k.val := by omega
  have hmod : (256 * k.val + a.val.toNat) % 256 = a.val.toNat := by omega
  simp [combTab, iotaTab, ofArr, Array.getD_eq_getD_getElem?, hi, hdiv, hmod, ha]

theorem coeff_combTab (M : ℕ) (l : Array GF128) (pk : ℕ → GF256) (off : ℕ) :
    coeff (combTab M l) M pk off =
      combineVec betaFast GF256.toBits (ofArr (n := M) l) fun k => pk (off + k) := by
  simp only [coeff, combineVec, Fin.foldl_eq_finRange_foldl, combTab_getD]

/-! ## The loaded variables -/

/-- The `N` variables `s_i = byteLoad β (o + i)` at `w`. -/
def byteVals (w : ℕ → GF128) (o N : ℕ) : Array GF128 :=
  (Array.range N).map fun i => (byteLoad betaFast (o + i)).eval w

/-- `s_i` from the array (and by evaluation beyond it, which the gadget never reads). -/
def loadFn (xs : Array GF128) (w : ℕ → GF128) (o : ℕ) : ℕ → GF128 := fun i =>
  if h : i < xs.size then xs[i] else (byteLoad betaFast (o + i)).eval w

theorem loadFn_byteVals (w : ℕ → GF128) (o N : ℕ) :
    loadFn (byteVals w o N) w o = fun i => (byteLoad betaFast (o + i)).eval w := by
  funext i
  unfold loadFn
  split_ifs with h <;> simp [byteVals]

/-! ## The gadget -/

/-- `qs_eval_combined_public_map(pk, s, l)` on values, with `tab = combTab M l`. -/
def publicMapFast (tab : Array GF128) (N M : ℕ) (pk : ℕ → GF256) (x : ℕ → GF128) : GF128 :=
  publicMapValue (fun m => coeff tab M pk m.off) N M x

/-- **The fast gadget is the generator's value**: `publicMapFast` on the tables is `Expr.eval` of
`evalCombinedPublicMap` at `β = betaFast`, `K = GF256`, `l = ofArr l`. -/
theorem publicMapFast_eq (l : Array GF128) (N M : ℕ) (pk : ℕ → GF256) (o : ℕ) (w : ℕ → GF128) :
    publicMapFast (combTab M l) N M pk (loadFn (byteVals w o N) w o) =
      (evalCombinedPublicMap betaFast GF256.toBits N M pk (fun i => byteLoad betaFast (o + i))
        (ofArr l)).eval w := by
  rw [eval_evalCombinedPublicMap, loadFn_byteVals, publicMapFast]
  simp only [coeff_combTab]

/-! ## The relations' evaluators -/

section Moussaka

open Moussaka Keccak

/-- `Moussaka.redeemValues` with the UOV terms by `publicMapFast` (the `N` loaded bytes of `s` are
shared by all Anchors). -/
def moussakaRedeemValues (anchors : List (ℕ → GF256)) (nf ctxIss ctxRed : ℕ → UInt8)
    (lArr : Array GF128) (w : ℕ → GF128) : List GF128 :=
  let tab := combTab M lArr
  let xs := byteVals w redeemOffS N
  let x := loadFn xs w redeemOffS
  let kv := qsKeccakValues w redeemOffStates 800 le_rfl
    ((qsInput (F := GF128) (redeemPub nf ctxIss ctxRed) redeemMap).map (Expr.eval w))
  let lq := (List.finRange anchors.length).foldl
    (fun acc (u : Fin anchors.length) => acc + w (selBit u) * publicMapFast tab N M anchors[u] x) 0
  (bitSystem (8 * redeemOffB) ++ selectorSystem anchors.length).values w ++ kv.1 ++
    [(loutExpr betaFast (ofArr lArr) (kv.2.map Expr.const)).eval w + lq]

theorem moussakaRedeemValues_eq (anchors : List (ℕ → GF256)) (nf ctxIss ctxRed : ℕ → UInt8)
    (lArr : Array GF128) (w : ℕ → GF128) :
    moussakaRedeemValues anchors nf ctxIss ctxRed lArr w =
      redeemValues betaFast GF256.toBits anchors nf ctxIss ctxRed (ofArr lArr) w := by
  simp only [moussakaRedeemValues, redeemValues, redeemOutput, lqExpr, Expr.eval_add,
    eval_foldl_add, Expr.eval_mul, Expr.eval_wit, Expr.eval_const, ← publicMapFast_eq]

end Moussaka

section Ratatouille

open Ratatouille Keccak

/-- `Ratatouille.spendValues` with the UOV term by `publicMapFast`. -/
def ratatouilleSpendValues (pk : ℕ → GF256) (nf : ℕ → UInt8) (d : ℕ) (cNext ctx : ℕ → UInt8)
    (lArr : Array GF128) (w : ℕ → GF128) : List GF128 :=
  let com := qsKeccakValues w 247 256 (by norm_num)
    ((qsInput (F := GF128) (comState nf ctx 0 zeros) spendComMap).map (Expr.eval w))
  let tag := qsKeccakValues w 447 360 (by norm_num)
    ((qsInput (F := GF128) (tagState zeros 0) spendTagMap).map (Expr.eval w))
  let nxt := qsKeccakValues w 647 256 (by norm_num)
    ((qsInput (F := GF128) (comState zeros ctx 0 zeros) spendComNextMap).map (Expr.eval w))
  let lp := publicMapFast (combTab uovM lArr) uovN uovM pk (loadFn (byteVals w 112 uovN) w 112)
  (List.range (8 * spendWitnessBytes)).map (fun i => w i * (w i + 1)) ++
    (spendSum1 (F := GF128)).1.map (Expr.eval w) ++ (spendSum2 d).1.map (Expr.eval w) ++
    (conservation d).map (Expr.eval w) ++
    com.1 ++ (List.finRange 256).map (fun i : Fin 256 => com.2[i] + w (8 * 32 + i.1)) ++
    tag.1 ++ [(tagCombination betaFast (ofArr lArr) (tag.2.map Expr.const)).eval w + lp] ++
    nxt.1 ++ (List.finRange 256).map (fun i : Fin 256 => nxt.2[i] + bitF (byteBit cNext i.1))

theorem ratatouilleSpendValues_eq (pk : ℕ → GF256) (nf : ℕ → UInt8) (d : ℕ)
    (cNext ctx : ℕ → UInt8) (lArr : Array GF128) (w : ℕ → GF128) :
    ratatouilleSpendValues pk nf d cNext ctx lArr w =
      spendValues betaFast GF256.toBits pk nf d cNext ctx (ofArr lArr) w := by
  simp only [ratatouilleSpendValues, spendValues, combinedConstraint, Expr.eval_add,
    publicMapFast_eq]

end Ratatouille

section PomFRIT

open PomFRIT

/-- `System.values (PomFRIT.pomfritRedeemSystem …)` with the UOV term by `publicMapFast`. -/
def pomfritRedeemValues (N M : ℕ) (pk : ℕ → GF256) (h : Fin M → GF256) (lArr : Array GF128)
    (w : ℕ → GF128) : List GF128 :=
  (List.range (witnessBits N M)).map (fun i => (bitConstraint (Expr.wit i)).eval w) ++
    [publicMapFast (combTab M lArr) N M pk (loadFn (byteVals w (witOffS M) N) w (witOffS M)) +
      ((linComb (ofArr (n := M) lArr) fun k => byteLoad betaFast (witOffR + k)) +
        Expr.const (combineVec betaFast GF256.toBits (ofArr lArr) h)).eval w]

theorem pomfritRedeemValues_eq (N M : ℕ) (pk : ℕ → GF256) (h : Fin M → GF256)
    (lArr : Array GF128) (w : ℕ → GF128) :
    pomfritRedeemValues N M pk h lArr w =
      (pomfritRedeemSystem betaFast GF256.toBits N M pk h (ofArr lArr)).values w := by
  simp only [pomfritRedeemValues, pomfritRedeemSystem, System.values, List.map_append,
    List.map_map, List.map_singleton, Function.comp_def, outputConstraint, Expr.eval_add,
    publicMapFast_eq]

end PomFRIT

end UovEval

end VoleMole.Verifier
