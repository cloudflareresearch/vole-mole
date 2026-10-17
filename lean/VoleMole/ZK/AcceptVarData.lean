import VoleMole.ZK.AcceptCount

/-!
# The second moment of the open count: the kernel's passes (`lean/docs/zk.md` §10.1)

The computations behind `Accept.card_accSet_ge_114` (`ZK/AcceptVar.lean`), which bounds the
grinding acceptance set by the second moment of the open count on the box `S = [0, 120)¹⁷`
instead of the first.

* `go2`: one pass over the tree that returns, for the subtree of `v`, the leaf counts `c v`
  (as `go`), the list of the counts `c w` of the internal nodes `w` below `v` (`v` included), and
  the sum over the internal nodes `w'` below `v` of `Σ_{w below w'} (P(c w') − P(c w' + c w))`,
  where `P(a) = Π_i (120 − a_i)` (`V17.u`) is the number of tuples of `S` that avoid a set of
  leaves with counts `a`. The lists add up to `Σ_v depth(v) ≈ 25 000` entries.
* `hist`: the histogram of a list of count vectors. The `2303` internal nodes have only `136`
  distinct count vectors, so the sum over all ordered pairs of internal nodes of
  `P(c v + c w)` (`aAll`) costs `136²` products instead of `2303²`.

Each value below is one `decide +kernel` (about 25 s each).
-/

namespace VoleMole.ZK.Accept

/-- Componentwise equality of count vectors, by `Nat.beq` (which the kernel evaluates on
literals). -/
def V17.beq (a b : V17) : Bool :=
  Nat.beq a.x0 b.x0 && Nat.beq a.x1 b.x1 && Nat.beq a.x2 b.x2 && Nat.beq a.x3 b.x3 &&
  Nat.beq a.x4 b.x4 && Nat.beq a.x5 b.x5 && Nat.beq a.x6 b.x6 && Nat.beq a.x7 b.x7 &&
  Nat.beq a.x8 b.x8 && Nat.beq a.x9 b.x9 && Nat.beq a.x10 b.x10 && Nat.beq a.x11 b.x11 &&
  Nat.beq a.x12 b.x12 && Nat.beq a.x13 b.x13 && Nat.beq a.x14 b.x14 && Nat.beq a.x15 b.x15 &&
  Nat.beq a.x16 b.x16

/-- **One pass over the subtree of `v`** (with `f` levels of fuel): the counts `c v`, the counts
of the internal nodes below `v` (`v` first), and the sum over the internal nodes `w'` below `v`
of `Σ_{w below w'} (P(c w') − P(c w' + c w))`. -/
def go2 : ℕ → ℕ → V17 × List V17 × ℕ
  | 0, v => (leafVec v, [], 0)
  | f + 1, v =>
    if v < 2303 then
      match go2 f (2 * v + 1), go2 f (2 * v + 2) with
      | (a, la, s), (b, lb, t) =>
        let c := a.add b
        let l := c :: (la ++ lb)
        (c, l, s + t + (l.map fun y => c.u - (c.add y).u).sum)
    else (leafVec v, [], 0)

/-- Add one occurrence of `a` to a histogram. -/
def hins (a : V17) : List (V17 × ℕ) → List (V17 × ℕ)
  | [] => [(a, 1)]
  | (x, n) :: t => if V17.beq a x then (x, n + 1) :: t else (x, n) :: hins a t

/-- The histogram of a list. -/
def hist (L : List V17) : List (V17 × ℕ) := L.foldl (fun h a => hins a h) []

/-- The counts of the `2303` internal nodes. -/
def L0 : List V17 := (go2 13 0).2.1

/-- `Σ_{x, y} n_x n_y P(x + y)` over a histogram. -/
def aAll (H : List (V17 × ℕ)) : ℕ :=
  (H.map fun p => p.2 * (H.map fun q => q.2 * (p.1.add q.1).u).sum).sum

set_option maxRecDepth 200000

/-- The related pairs' sum. -/
theorem rd_val : (go2 13 0).2.2 = 72875678509543480965805498961646914158 := by decide +kernel

/-- The all-pairs sum. -/
theorem aAll_val : aAll (hist L0) = 1056881111883048691624339931618558395936896 := by
  decide +kernel

/-- `Σ_v P(c v)`. -/
theorem sz_val : ((hist L0).map fun p => p.2 * p.1.u).sum =
    484259924132640697798742136587093743952 := by decide +kernel

/-- `Σ_v (P(c v) − P(2 c v))`. -/
theorem rs_val : ((hist L0).map fun p => p.2 * (p.1.u - (p.1.add p.1).u)).sum =
    19311176279936440689791419079891556688 := by decide +kernel

end VoleMole.ZK.Accept
