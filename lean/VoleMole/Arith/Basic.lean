import Mathlib

/-!
# Constraint systems as QuickSilver sees them

The shared interface for the executable arithmetization models (`VoleMole/Arith/*`). A relation's
constraint generator is modelled as a Lean function that produces a `System F`: the list of
expressions passed to `add_constraint`, in order. Following `lean/docs/extraction/L7-uov.md` §0, the *value*
of a constraint at committed values `w* ∈ F^ℓ` is the expression evaluated with field arithmetic
in `F`; degree lifts and type conversions (`qs_to_gfsecpar`, `qs_lift`, `qs_mul`) are the identity
on values.

Generators are written over an arbitrary field `F` of characteristic 2, with every public constant
they need (the GF(256) embedding `β`, the combination coefficients `l`, …) passed in as arguments.
Soundness and completeness are proved over this abstract `F`. The executable instance for
differential testing against the C++ uses the concrete GF(2¹²⁸) of `VoleMole/Arith/GF.lean` and maps
expressions across with `Expr.map`.

Witness indices are bit indices (`get_witness_bit(i)`); byte loads are expanded to
`Σ_b β_b · wit (8o+b)` (`byteLoad`).
-/

namespace VoleMole.Arith

/-- A constraint expression: witness bits, public constants, `+` and `*`. -/
inductive Expr (F : Type*) where
  | wit : ℕ → Expr F
  | const : F → Expr F
  | add : Expr F → Expr F → Expr F
  | mul : Expr F → Expr F → Expr F
  deriving Inhabited

namespace Expr

variable {F G : Type*}

instance : Add (Expr F) := ⟨add⟩
instance : Mul (Expr F) := ⟨mul⟩

/-- The value of an expression at committed values `w`. -/
def eval [Add F] [Mul F] (w : ℕ → F) : Expr F → F
  | wit i => w i
  | const c => c
  | add a b => eval w a + eval w b
  | mul a b => eval w a * eval w b

/-- Formal degree, as QuickSilver tracks it (constants have degree 0). -/
def degree : Expr F → ℕ
  | wit _ => 1
  | const _ => 0
  | add a b => max a.degree b.degree
  | mul a b => a.degree + b.degree

/-- Witness indices read by an expression (with repetitions). -/
def support : Expr F → List ℕ
  | wit i => [i]
  | const _ => []
  | add a b => a.support ++ b.support
  | mul a b => a.support ++ b.support

/-- Change the coefficient field, e.g. from an abstract `F` to the concrete GF(2¹²⁸). -/
def map (f : F → G) : Expr F → Expr G
  | wit i => wit i
  | const c => const (f c)
  | add a b => add (a.map f) (b.map f)
  | mul a b => mul (a.map f) (b.map f)

@[simp] theorem eval_wit [Add F] [Mul F] (w : ℕ → F) (i : ℕ) : (wit i).eval w = w i := rfl
@[simp] theorem eval_const [Add F] [Mul F] (w : ℕ → F) (c : F) : (const c).eval w = c := rfl
@[simp] theorem eval_add [Add F] [Mul F] (w : ℕ → F) (a b : Expr F) :
    (a + b).eval w = a.eval w + b.eval w := rfl
@[simp] theorem eval_mul [Add F] [Mul F] (w : ℕ → F) (a b : Expr F) :
    (a * b).eval w = a.eval w * b.eval w := rfl

theorem eval_map [NonUnitalNonAssocSemiring F] [NonUnitalNonAssocSemiring G] (f : F →ₙ+* G)
    (w : ℕ → F) (e : Expr F) : (e.map f).eval (f ∘ w) = f (e.eval w) := by
  induction e with
  | wit i => rfl
  | const c => rfl
  | add a b iha ihb => simp only [map, eval, iha, ihb, map_add]
  | mul a b iha ihb => simp only [map, eval, iha, ihb, map_mul]

end Expr

/-- A constraint system: the `add_constraint` arguments, in order. -/
abbrev System (F : Type*) := List (Expr F)

/-- All constraints vanish at `w`. -/
def System.Holds {F : Type*} [Add F] [Mul F] [Zero F] (cs : System F) (w : ℕ → F) : Prop :=
  ∀ e ∈ cs, e.eval w = 0

/-- The constraint values at `w`, in order (what the differential tests compare). -/
def System.values {F : Type*} [Add F] [Mul F] (cs : System F) (w : ℕ → F) : List F :=
  cs.map (Expr.eval w)

theorem System.holds_append {F : Type*} [Add F] [Mul F] [Zero F] (a b : System F) (w : ℕ → F) :
    (a ++ b).Holds w ↔ a.Holds w ∧ b.Holds w := by
  simp only [System.Holds, List.mem_append]
  constructor
  · intro h; exact ⟨fun e he => h e (Or.inl he), fun e he => h e (Or.inr he)⟩
  · rintro ⟨ha, hb⟩ e (he | he)
    exacts [ha e he, hb e he]

/-- A bit as a field element. -/
def bitF {F : Type*} [Zero F] [One F] (b : Bool) : F := if b then 1 else 0

/-- A bit vector as committed values. -/
def ofBits {F : Type*} [Zero F] [One F] (w : ℕ → Bool) : ℕ → F := fun i => bitF (w i)

/-- `load_witness_8_bits_and_combine(8o)`: `Σ_{b<8} β_b · w_{8o+b}`, summed left to right. -/
def byteLoad {F : Type*} (β : Fin 8 → F) (o : ℕ) : Expr F :=
  Expr.const (β 0) * Expr.wit (8 * o) + Expr.const (β 1) * Expr.wit (8 * o + 1) +
  Expr.const (β 2) * Expr.wit (8 * o + 2) + Expr.const (β 3) * Expr.wit (8 * o + 3) +
  Expr.const (β 4) * Expr.wit (8 * o + 4) + Expr.const (β 5) * Expr.wit (8 * o + 5) +
  Expr.const (β 6) * Expr.wit (8 * o + 6) + Expr.const (β 7) * Expr.wit (8 * o + 7)

theorem eval_byteLoad {F : Type*} [CommRing F] (β : Fin 8 → F) (o : ℕ) (w : ℕ → F) :
    (byteLoad β o).eval w = ∑ b : Fin 8, β b * w (8 * o + b) := by
  simp [byteLoad, Fin.sum_univ_eight]

/-- `add_bit_constraint(x)`: `x·(x+1)`. -/
def bitConstraint {F : Type*} [One F] (x : Expr F) : Expr F := x * (x + Expr.const 1)

end VoleMole.Arith
