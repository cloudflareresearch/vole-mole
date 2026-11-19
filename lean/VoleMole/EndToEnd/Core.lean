import VoleMole.Seed.QuickSilver
import VoleMole.Arith.Basic

/-!
# End to end, generic part: the extraction core applied to an `Arith.System`

This file joins the seed-extraction core (`SeedExtraction.lean`, L5–L6), the QuickSilver
top-coefficient argument (`Seed/QuickSilver.lean`, L4) and the arithmetization interface
(`Arith/Basic.lean`, L7). The per-relation theorems are in `EndToEnd/Relations.lean`.

1. **Translation** (`toQS`, `constraintQS`, `sysQS`). An `Arith.Expr` records values only:
   constants have degree 0 and a sum has the larger degree of its summands. The verifier's
   circuit (`QSExpr`) adds only values of equal degree, so `toQS` inserts the degree raisings
   (`raise`) that the C++ types insert, and `constraintQS d` raises the result to `d`
   (`add_constraint`). The translation is well formed, has degree exactly `Expr.degree`, and its
   value is `Expr.eval` (`toQS_wf`, `toQS_deg`, `value_toQS`).
2. **Top coefficient** (`sysCheckPoly_natDegree_coeff`): the check polynomial of an `Arith.System`
   of degree `≤ d` has degree `≤ d` and `X^d` coefficient `Σ_k χ_k f_k(w*)` with
   `f_k = (cs.get k).eval w*`. This is `checkPoly_natDegree_coeff` applied to `sysQS`.
3. **The verifier's computation** (`QSExpr.mac`, `qsCheck`). The verifier evaluates the circuit on
   the MACs `q_j = Q[j](Δ) + d_j·Δ` at the field element `Δ`. `eval_mac` shows this is the check
   polynomial evaluated at `Δ`, so the accepting condition can be stated on what the verifier
   computes, and the polynomial is built from L3's affine form (`claim3_of_system`).
4. **The combination challenge** (`extract_or_few`). The core is applied with
   `sat w := Wit (extW w)`, where `Wit` is the relation's witness predicate on committed values
   (bit vector whose decoding satisfies the relation). The chain's own system `cs` (built with the
   chain's `l`) enters only through two good-challenge hypotheses, which split L4's bad event:
   * `hQS`: if `cs` fails at `w*`, the top coefficient `Σ_k χ_k f_k(w*)` is nonzero (Schwartz–Zippel
     over `chall₂`, `card_zkHash_eq_zero_le`, applied for each fixed `l`);
   * `hcomb`: if `cs` holds at `w*`, then `w*` encodes a witness (over `l`, with `w*` fixed before
     `chall₂`: the relation's `*_sound_card`; deterministic for the issue relations).
   Together they cost `ε_QS(n) + 1/|F|`, L4 Proposition 3, and avoid any linearity-in-`l`
   argument: the "uncombined" constraints never have to be named.
-/

open Finset Polynomial

set_option linter.unusedSectionVars false

namespace VoleMole.EndToEnd

open VoleMole.Seed VoleMole.SeedExtraction
open VoleMole.Arith (Expr System bitF)

/-! ## 1. Translation `Arith.Expr → QSExpr` -/

section Translation

variable {F : Type*}

/-- The verifier's circuit for an `Arith.Expr`: constants at degree 0, and each summand raised to
the degree of the sum (as the C++ `qs_val` constructors do). -/
def toQS : Expr F → QSExpr F ℕ
  | .wit i => .input i
  | .const c => .const c 0
  | .add a b => .add (.raise (max a.degree b.degree - a.degree) (toQS a))
      (.raise (max a.degree b.degree - b.degree) (toQS b))
  | .mul a b => .mul (toQS a) (toQS b)

theorem toQS_deg : ∀ e : Expr F, (toQS e).deg = e.degree
  | .wit _ => rfl
  | .const _ => rfl
  | .add a b => by
      simp only [toQS, QSExpr.deg, toQS_deg a, Expr.degree]; omega
  | .mul a b => by simp only [toQS, QSExpr.deg, toQS_deg a, toQS_deg b, Expr.degree]

theorem toQS_wf : ∀ e : Expr F, (toQS e).WF
  | .wit _ => trivial
  | .const _ => trivial
  | .add a b => by
      refine ⟨toQS_wf a, toQS_wf b, ?_⟩
      simp only [QSExpr.deg, toQS_deg]; omega
  | .mul a b => ⟨toQS_wf a, toQS_wf b⟩

theorem value_toQS [Field F] (w : ℕ → F) : ∀ e : Expr F, (toQS e).value w = e.eval w
  | .wit _ => rfl
  | .const _ => rfl
  | .add a b => by simp only [toQS, QSExpr.value, value_toQS w a, value_toQS w b, Expr.eval]
  | .mul a b => by simp only [toQS, QSExpr.value, value_toQS w a, value_toQS w b, Expr.eval]

/-- `add_constraint`: the constraint's circuit raised to degree `d`. -/
def constraintQS (d : ℕ) (e : Expr F) : QSExpr F ℕ := .raise (d - e.degree) (toQS e)

theorem constraintQS_wf_deg (d : ℕ) (e : Expr F) (he : e.degree ≤ d) :
    (constraintQS d e).WF ∧ (constraintQS d e).deg = d := by
  refine ⟨toQS_wf e, ?_⟩
  simp only [constraintQS, QSExpr.deg, toQS_deg]; omega

theorem value_constraintQS [Field F] (d : ℕ) (w : ℕ → F) (e : Expr F) :
    (constraintQS d e).value w = e.eval w := value_toQS w e

/-- The verifier's circuits for a system, indexed by constraint position. -/
def sysQS (cs : System F) (d : ℕ) : Fin cs.length → QSExpr F ℕ := fun k => constraintQS d (cs.get k)

/-- The constraint values `f_k(w) = (cs.get k).eval w`, as a vector. -/
def valVec [Add F] [Mul F] (cs : System F) (w : ℕ → F) : Fin cs.length → F :=
  fun k => (cs.get k).eval w

theorem holds_iff_valVec_eq_zero [Add F] [Mul F] [Zero F] (cs : System F) (w : ℕ → F) :
    cs.Holds w ↔ valVec cs w = 0 := by
  constructor
  · intro h; funext k; exact h _ (List.get_mem cs k)
  · intro h e he
    obtain ⟨k, rfl⟩ := List.get_of_mem he
    exact congrFun h k

end Translation

/-! ## 2. The check polynomial of a system -/

section Check

variable {F : Type*} [Field F]

/-- The QuickSilver check polynomial of the system `cs` at degree `d`. -/
noncomputable def sysCheckPoly (q : ℕ → F[X]) (cs : System F) (d : ℕ) (χ : Fin cs.length → F)
    (R : F[X]) : F[X] :=
  checkPoly q (sysQS cs d) χ R

/-- **Top coefficient for an `Arith.System`.** If every constraint has degree `≤ d`, the witness
MACs are affine with slopes `w*`, and the remainder has degree `≤ d − 1`, then the check
polynomial has degree `≤ d` and `X^d` coefficient `Σ_k χ_k f_k(w*)`. -/
theorem sysCheckPoly_natDegree_coeff {d : ℕ} (hd : 1 ≤ d) (cs : System F)
    (hdeg : ∀ e ∈ cs, e.degree ≤ d) (q : ℕ → F[X]) (w : ℕ → F)
    (hq : ∀ j, (q j).natDegree ≤ 1 ∧ (q j).coeff 1 = w j) (χ : Fin cs.length → F) (R : F[X])
    (hR : R.natDegree ≤ d - 1) :
    (sysCheckPoly q cs d χ R).natDegree ≤ d ∧
      (sysCheckPoly q cs d χ R).coeff d = ∑ k, χ k * valVec cs w k := by
  have := checkPoly_natDegree_coeff hd q w hq (sysQS cs d)
    (fun k => constraintQS_wf_deg d _ (hdeg _ (List.get_mem cs k))) χ R hR
  simpa only [sysCheckPoly, valVec, sysQS, value_constraintQS] using this

end Check

/-! ## 3. What the verifier computes -/

namespace QSExprMac

variable {F ι : Type*} [Field F]

/-- The verifier's MAC of a circuit, given the witness MACs `m` and the global key `Δ`: constants
at degree `e` are `c·Δ^e`, raising by `k` multiplies by `Δ^k`, and `+`, `×` are field
operations (`quicksilver.hpp`, verifier branch; L4 §2). -/
def mac (m : ι → F) (Δ : F) : QSExpr F ι → F
  | .input j => m j
  | .const c e => c * Δ ^ e
  | .add a b => mac m Δ a + mac m Δ b
  | .mul a b => mac m Δ a * mac m Δ b
  | .raise k a => mac m Δ a * Δ ^ k

/-- The verifier's MAC is the polynomial MAC evaluated at `Δ`. -/
theorem eval_mac (q : ι → F[X]) (Δ : F) :
    ∀ E : QSExpr F ι, (E.eval q).eval Δ = mac (fun j => (q j).eval Δ) Δ E
  | .input _ => rfl
  | .const c e => by simp [QSExpr.eval, mac]
  | .add a b => by simp [QSExpr.eval, mac, eval_mac q Δ a, eval_mac q Δ b]
  | .mul a b => by simp [QSExpr.eval, mac, eval_mac q Δ a, eval_mac q Δ b]
  | .raise k a => by simp [QSExpr.eval, mac, eval_mac q Δ a]

end QSExprMac

open QSExprMac

/-- The ZKHash combination `Σ_k χ_k m_k` of the constraint MACs, as the verifier computes it from
the witness MACs `m` at key `Δ`. -/
def qsCheck {F : Type*} [Field F] (cs : System F) (d : ℕ) (χ : Fin cs.length → F) (m : ℕ → F)
    (Δ : F) : F :=
  ∑ k, χ k * mac m Δ (sysQS cs d k)

theorem eval_sysCheckPoly {F : Type*} [Field F] (q : ℕ → F[X]) (cs : System F) (d : ℕ)
    (χ : Fin cs.length → F) (R : F[X]) (Δ : F) :
    (sysCheckPoly q cs d χ R).eval Δ = qsCheck cs d χ (fun j => (q j).eval Δ) Δ + R.eval Δ := by
  simp [sysCheckPoly, checkPoly, qsCheck, eval_finsetSum, eval_mac]

/-! ## 4. The extraction core instantiated with a system -/

section Core

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]
variable {B : ι → Type*} [∀ i, AddCommGroup (B i)]

/-- Committed values on the `ℓ` witness rows, extended by `0` to the index type `ℕ` of
`Arith.Expr.wit`. -/
def extW {ℓ : ℕ} (w : Fin ℓ → F) : ℕ → F := fun i => if h : i < ℓ then w ⟨i, h⟩ else 0

/-- The extractor's candidate from tree `i`: `w^{(i)} = u^{(i)} + d`, as committed values. -/
def candidate {ℓ : ℕ} (u : ι → Fin ℓ → Bool) (dc : Fin ℓ → Bool) (i : ι) : ℕ → F :=
  extW fun j => bit (u i j) + bit (dc j)

/-- The verifier's witness MACs after the correction step (`voleith.hpp`, `q_j ← Q[j] + d_j·Δ`),
extended by `0`. -/
def macs {ℓ : ℕ} (e : (∀ i, B i) →+ F) (Q : Fin ℓ → (∀ i, B i) → F) (dc : Fin ℓ → Bool)
    (Δ : ∀ i, B i) : ℕ → F :=
  extW fun j => Q j Δ + bit (dc j) * e Δ

/-- **Claim 3 for an `Arith.System`.** On a chain whose witness rows are affine on `A` with slopes
`u*` (`Claim4Hyp.consistent`, from L3), the verifier's check value
`qsCheck(macs Δ, e Δ) + R(e Δ)` vanishes on `A`, and the remainder `R` (masks, `ã`, the prover's
check value) has degree `≤ d − 1`. If the top coefficient `Σ_k χ_k f_k(w*)` is nonzero whenever
`cs` fails at `w* = u* + d`, then `cs` holds at `w*` or `|A| ≤ d`. -/
theorem claim3_of_system [DecidableEq F] {ℓ d : ℕ} (hd : 1 ≤ d) {e : (∀ i, B i) →+ F}
    (he : Function.Injective e) {A : Finset (∀ i, B i)} {Q : Fin ℓ → (∀ i, B i) → F}
    {uStar : Fin ℓ → F} (hcons : ∀ j, ∃ v, ∀ Δ ∈ A, Q j Δ = v + uStar j * e Δ)
    (dc : Fin ℓ → Bool) (cs : System F) (hdeg : ∀ x ∈ cs, x.degree ≤ d)
    (χ : Fin cs.length → F) (R : F[X]) (hR : R.natDegree ≤ d - 1)
    (hacc : ∀ Δ ∈ A, qsCheck cs d χ (macs e Q dc Δ) (e Δ) + R.eval (e Δ) = 0)
    (hQS : ¬cs.Holds (extW (uStar + fun j => bit (dc j))) →
      ∑ k, χ k * valVec cs (extW (uStar + fun j => bit (dc j))) k ≠ 0) :
    cs.Holds (extW (uStar + fun j => bit (dc j))) ∨ A.card ≤ d := by
  classical
  choose v hv using hcons
  set w : ℕ → F := extW (uStar + fun j => bit (dc j))
  -- L3's affine form, after the correction, as polynomials.
  let q : ℕ → F[X] := fun i =>
    if h : i < ℓ then C (v ⟨i, h⟩) + C (uStar ⟨i, h⟩ + bit (dc ⟨i, h⟩)) * X else 0
  have hq : ∀ j, (q j).natDegree ≤ 1 ∧ (q j).coeff 1 = w j := by
    intro j
    by_cases h : j < ℓ
    · simp only [q, w, extW, h, dite_true, Pi.add_apply]
      refine ⟨(natDegree_add_le _ _).trans (max_le (by simp) ?_), by simp⟩
      simpa using natDegree_C_mul_X_pow_le (uStar ⟨j, h⟩ + bit (dc ⟨j, h⟩)) 1
    · simp [q, w, extW, h]
  have hroot : ∀ Δ ∈ A, (sysCheckPoly q cs d χ R).eval (e Δ) = 0 := by
    intro Δ hΔ
    rw [eval_sysCheckPoly, ← hacc Δ hΔ]
    congr 2
    funext i
    by_cases h : i < ℓ
    · simp only [q, macs, extW, h, dite_true, eval_add, eval_C, eval_mul, eval_X, hv _ Δ hΔ]
      ring
    · simp [q, macs, extW, h]
  obtain ⟨hdeg', htop⟩ := sysCheckPoly_natDegree_coeff hd cs hdeg q w hq χ R hR
  exact claim3_of_good he hdeg' htop hroot hQS

/-- **The extraction core with a real constraint system (generic form).**

Fix one chain. Hypotheses:
* `hK`: `Claim4Hyp` on the accepting set `A` (L1, L2, L5's `tree_form`, L3's `consistent` via
  `claim4Hyp_of_kosGood`), with `u*` the canonical slope fixed before `chall₂` (L4 §5);
* `dc`: the correction `d`, a bit vector;
* `cs`: the chain's constraint system (with the chain's `l`), every constraint of degree `≤ d`;
* `hacc`: on `A`, the verifier's check value vanishes (accepting), with remainder `R` of degree
  `≤ d − 1` (L3 on the mask rows; `maskPoly_natDegree_le`);
* `hQS`: good `chall₂`, Schwartz–Zippel part (L4 Prop. 2);
* `hcomb`: good `l`, `cs` holding at `w*` implies `Wit w*` (L7's `*_sound_card`);
* `hWbits`: `Wit` implies that the `ℓ` witness rows are bits (true of every relation's `Wit`);
* `hclaim1`: accepted admissible `chall₃` decode into `A` (L1).

Conclusion: some known tree's candidate `w^{(i)} = u^{(i)} + d` satisfies `Wit`, or at most
`max(d, 1)` admissible `chall₃` are accepted. -/
theorem extract_or_few [CharP F 2] [DecidableEq F] {Ch : Type*} {ℓ d : ℕ} (hd : 1 ≤ d)
    {e : (∀ i, B i) →+ F} {A : Finset (∀ i, B i)} {known : Finset ι} {u : ι → Fin ℓ → Bool}
    {Q : Fin ℓ → (∀ i, B i) → F} {uStar : Fin ℓ → F}
    (hK : Claim4Hyp e (A : Set (∀ k, B k)) known u Q uStar) (dc : Fin ℓ → Bool)
    (cs : System F) (hdeg : ∀ x ∈ cs, x.degree ≤ d) (Wit : (ℕ → F) → Prop)
    (hWbits : ∀ w, Wit w → ∀ j < ℓ, w j = 0 ∨ w j = 1)
    (χ : Fin cs.length → F) (R : F[X]) (hR : R.natDegree ≤ d - 1)
    (hacc : ∀ Δ ∈ A, qsCheck cs d χ (macs e Q dc Δ) (e Δ) + R.eval (e Δ) = 0)
    (hQS : ¬cs.Holds (extW (uStar + fun j => bit (dc j))) →
      ∑ k, χ k * valVec cs (extW (uStar + fun j => bit (dc j))) k ≠ 0)
    (hcomb : cs.Holds (extW (uStar + fun j => bit (dc j))) →
      Wit (extW (uStar + fun j => bit (dc j))))
    (Z : Finset Ch) (δ : Ch → ∀ i, B i) (hδ : Set.InjOn δ Z) (acc : Ch → Prop)
    [DecidablePred acc] (hclaim1 : ∀ x ∈ Z, acc x → δ x ∈ A) :
    (∃ i ∈ known, Wit (candidate u dc i)) ∨ #{x ∈ Z | acc x} ≤ max d 1 := by
  have hclaim3 : Wit (extW (uStar + fun j => bit (dc j))) ∨ A.card ≤ d :=
    (claim3_of_system hd hK.lift_inj (fun j => hK.consistent j) dc cs hdeg χ R hR
      (fun Δ hΔ => hacc Δ hΔ) hQS).imp_left hcomb
  have hbits : Wit (extW (uStar + fun j => bit (dc j))) → ∀ j, uStar j = 0 ∨ uStar j = 1 := by
    intro hW
    refine bits_of_bit_constraints (uStar + fun j => bit (dc j)) uStar (fun j => bit (dc j))
      (fun j => ?_) (fun j => by cases dc j <;> simp [bit]) rfl
    have := hWbits _ hW j j.isLt
    simp only [extW, j.isLt, dite_true] at this
    rcases this with h | h <;> simp [h, CharTwo.add_self_eq_zero]
  exact accepting_card_le hK (fun w => Wit (extW w)) (fun j => bit (dc j)) d hclaim3 hbits Z δ
    hδ acc hclaim1

/-- `w* = u* + d`, the committed values fixed before `chall₂` (L4 §5), extended by `0`. -/
abbrev wStar {ℓ : ℕ} (uStar : Fin ℓ → F) (dc : Fin ℓ → Bool) : ℕ → F :=
  extW (uStar + fun j => bit (dc j))

/-- A witness predicate of the form "the `ℓ` rows are bits `wb` and `P wb`" forces bits. -/
theorem bits_of_exists_bitF {ℓ : ℕ} {P : (ℕ → Bool) → Prop} (w : ℕ → F)
    (h : ∃ wb : ℕ → Bool, (∀ i < ℓ, w i = bitF (wb i)) ∧ P wb) : ∀ j < ℓ, w j = 0 ∨ w j = 1 := by
  obtain ⟨wb, hw, -⟩ := h
  intro j hj
  rw [hw j hj]
  cases wb j <;> simp [bitF]

/-- **`extract_or_few` with the ZKHash weights.** `χ_k = zkCoeff n r₀ r₁ s t k` for
`chall₂ = (r₀, r₁, s, t)`, so the top coefficient is `zkHash` of the constraint values
(`zkHash_eq_sum`), the event bounded by `card_qs_bad_le`. -/
theorem extract_or_few_zk [CharP F 2] [DecidableEq F] {Ch : Type*} {ℓ d : ℕ} (hd : 1 ≤ d)
    {e : (∀ i, B i) →+ F} {A : Finset (∀ i, B i)} {known : Finset ι} {u : ι → Fin ℓ → Bool}
    {Q : Fin ℓ → (∀ i, B i) → F} {uStar : Fin ℓ → F}
    (hK : Claim4Hyp e (A : Set (∀ k, B k)) known u Q uStar) (dc : Fin ℓ → Bool)
    (cs : System F) (hdeg : ∀ x ∈ cs, x.degree ≤ d) (Wit : (ℕ → F) → Prop)
    (hWbits : ∀ w, Wit w → ∀ j < ℓ, w j = 0 ∨ w j = 1)
    (r₀ r₁ s t : F) (R : F[X]) (hR : R.natDegree ≤ d - 1)
    (hacc : ∀ Δ ∈ A,
      qsCheck cs d (zkCoeff cs.length r₀ r₁ s t) (macs e Q dc Δ) (e Δ) + R.eval (e Δ) = 0)
    (hQS : ¬cs.Holds (wStar uStar dc) →
      zkHash cs.length r₀ r₁ s t (valVec cs (wStar uStar dc)) ≠ 0)
    (hcomb : cs.Holds (wStar uStar dc) → Wit (wStar uStar dc))
    (Z : Finset Ch) (δ : Ch → ∀ i, B i) (hδ : Set.InjOn δ Z) (acc : Ch → Prop)
    [DecidablePred acc] (hclaim1 : ∀ x ∈ Z, acc x → δ x ∈ A) :
    (∃ i ∈ known, Wit (candidate u dc i)) ∨ #{x ∈ Z | acc x} ≤ max d 1 :=
  extract_or_few hd hK dc cs hdeg Wit hWbits _ R hR hacc
    (fun h => by rw [← zkHash_eq_sum]; exact hQS h) hcomb Z δ hδ acc hclaim1

/-! ### The bad-challenge counts behind `hQS` -/

/-- **`hQS` fails rarely (L4 Prop. 2, per fixed system).** With `χ = zkCoeff n r₀ r₁ s t` (the
ZKHash weights from `chall₂ = (r₀, r₁, s, t)`), the top coefficient is `zkHash` of the constraint
values. If the system fails at `w`, at most `|F|²|S| + (n−1)²|F|²` of the `|F|³|S|` challenges make
it vanish. For a system that depends on `l`, apply this for each fixed `l` and average (the joint
`(chall₂, l)` count of `card_combined_bad_le`). -/
theorem card_qs_bad_le [Fintype F] [DecidableEq F] (cs : System F) (w : ℕ → F)
    (hfail : ¬cs.Holds w) (S : Finset F) :
    #{x ∈ chalSpace S | ∑ k, zkCoeff cs.length x.1 x.2.1 x.2.2.1 x.2.2.2 k * valVec cs w k = 0} ≤
      Fintype.card F * Fintype.card F * #S +
        (cs.length - 1) * (cs.length - 1) * (Fintype.card F * Fintype.card F) := by
  have hf : valVec cs w ≠ 0 := fun h => hfail ((holds_iff_valVec_eq_zero cs w).2 h)
  simpa only [zkHash_eq_sum] using card_zkHash_eq_zero_le hf S

end Core

end VoleMole.EndToEnd
