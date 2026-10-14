import VoleMole.Verifier.CrtGen

/-!
# Regenerating the CRT VOLE tables (port of `vole_mult_tables.py`)

A transcription of the table generator of faest-arch-opt
(`subprojects/faest-arch-opt/tools/vole_mult_tables.py`, run by its build as `--preset 128f` with
the default `--maxd 10 --maxe 10`), restricted to what the `128f` tables need, so that `F`, `G`,
`W_tree` and `W_gate` of `CrtData` are regenerated rather than only checked:

* the tree moduli: FAEST's tree depths (`faest_tree_spec`: one tree of depth 8, sixteen of
  depth 7 for `λ − w = 120`, `τ = 17`), each the lexicographically smallest irreducibles of that
  degree (`run_set`);
* the cost search (`full_cost`, `short_cost`, `place_gate_cost`, `crt_search`): Karatsuba-style
  splits, Montgomery's 13-gate five-term formula, the F₄-tower field multiplications (degree 6:
  15, degree 8: 24 gates), and the exact multiple-choice knapsack over places (powers of `x`,
  `x + 1`, infinity, the degree-2 irreducible; distinct irreducibles of degree ≥ 3, tree moduli
  excluded), with the script's tie-breaking (strict improvement, Python `dict` insertion order);
* the bilinear algorithms (`full_alg`, `short_alg`, `place_alg`, `tower_place_alg`,
  `mont5_alg`), the global interpolation (`left_inverse`, the same Gaussian elimination, since the
  evaluation map is not square), `build_tables` and `prune`.

Only the search's choices matter for agreement: any correct construction satisfies the bilinear
identity that `CrtGen.identityOk` checks, but the tables are compared entry by entry
(`regenOk`, run by `lake exe verifier_vectors`). Polynomials over `F₂` and `F₂`-vectors are
`Nat` bit vectors (bit `i` is the coefficient of `xⁱ`), elements of F₄ = F₂[w]/(w² + w + 1) are
`0 … 3` (`u + 2v` for `u + v·w`), as in the script.
-/

namespace VoleMole.Verifier.CrtSearch

open CrtGen

/-! ## Polynomials over F₂ and F₂-linear maps -/

/-- `pdeg` for nonzero polynomials. -/
def pdeg (a : Nat) : Nat := a.log2

/-- `bits_iter`: the set bits, in increasing order. -/
def bits (x : Nat) : List Nat := (List.range (x.log2 + 1)).filter x.testBit

/-- `combine`: XOR of `rows[i]` over the set bits `i` of `mask`. -/
def combine (mask : Nat) (rows : Array Nat) : Nat :=
  (bits mask).foldl (fun acc i => acc ^^^ rows.getD i 0) 0

def parity (x : Nat) : Bool := dot x x

def ppow (p e : Nat) : Nat := (List.range e).foldl (fun r _ => pmul r p) 1

def pmulmod (a b m : Nat) : Nat := pmod (pmul a b) m

partial def pgcd (a b : Nat) : Nat := if b == 0 then a else pgcd b (pmod a b)

/-- `x^(2^k) mod f`. -/
def xPow2k (f k : Nat) : Nat := (List.range k).foldl (fun r _ => pmulmod r r f) (pmod 2 f)

/-- The prime factors of `n`. -/
def primeFactors (n : Nat) : List Nat :=
  (List.range (n + 1)).filter fun q =>
    2 ≤ q && n % q == 0 && (List.range q).all fun r => r < 2 || q % r != 0

/-- `is_irreducible` (Rabin's test). -/
def isIrreducible (f : Nat) : Bool :=
  let n := pdeg f
  if f < 2 then false
  else if n == 1 then true
  else if f % 2 == 0 then false
  else if xPow2k f n != pmod 2 f then false
  else (primeFactors n).all fun q => pgcd f (pmod (xPow2k f (n / q) ^^^ 2) f) == 1

/-- `irreducibles_of_degree d`, in increasing order. -/
def irreducibles (d : Nat) : List Nat :=
  (List.range (2 ^ d)).filterMap fun k => if isIrreducible (2 ^ d + k) then some (2 ^ d + k) else none

#guard irreducibles 2 == [7] && irreducibles 3 == [0xb, 0xd] && (irreducibles 8).length == 30

/-- `reduction_rows q ncols`: row `i` of the map `(c_0 … c_{ncols−1}) ↦` coefficient `i` of
`(Σ c_j x^j) mod q`. -/
def reductionRows (q ncols : Nat) : Array Nat := Id.run do
  let mut rows := Array.replicate (pdeg q) 0
  let mut cur := 1
  for j in [0:ncols] do
    for i in bits cur do
      rows := rows.modify i (· ||| (1 <<< j))
    cur := pmod (cur <<< 1) q
  return rows

/-- `pascal_rows e`: the substitution `x ↦ x + 1` on polynomials of degree `< e`. -/
def pascalRows (e : Nat) : Array Nat :=
  (Array.range e).map fun i =>
    (List.range e).foldl (fun acc j => if i &&& j == i then acc ||| (1 <<< j) else acc) 0

/-- `left_inverse rows ncols`: `X` with `X · rows = I` (`X[c]` a mask over the row indices), by the
script's elimination (pivot: the first unused row with bit `c`). Empty if `rows` is not injective. -/
def leftInverse (rows : Array Nat) (ncols : Nat) : Array Nat := Id.run do
  let m := rows.size
  let mut wr := rows
  let mut wt : Array Nat := (Array.range m).map (1 <<< ·)
  let mut used := Array.replicate m false
  let mut piv : Array Nat := Array.replicate ncols 0
  for c in [0:ncols] do
    let mut p? : Option Nat := none
    for i in [0:m] do
      if p?.isNone && !used[i]! && wr[i]!.testBit c then p? := some i
    let some p := p? | return #[]
    used := used.set! p true
    piv := piv.set! c p
    let pr := wr[p]!
    let pt := wt[p]!
    for i in [0:m] do
      if i != p && wr[i]!.testBit c then
        wr := wr.set! i (wr[i]! ^^^ pr)
        wt := wt.set! i (wt[i]! ^^^ pt)
  return (Array.range ncols).map fun c => wt[piv[c]!]!

/-! ## Bilinear algorithms -/

/-- `Alg`: `gates[l] = (f, g)`, linear forms over the two inputs (`na`, `nb` bits); `W[q]` is a mask
over the gates giving output coordinate `q`. -/
structure Alg where
  na : Nat
  nb : Nat
  gates : Array (Nat × Nat)
  W : Array Nat
  deriving Inhabited

def Alg.base : Alg := ⟨1, 1, #[(1, 1)], #[1]⟩

/-- `precompose alg Ar Br na nb`. -/
def precompose (alg : Alg) (Ar Br : Array Nat) (na nb : Nat) : Alg :=
  ⟨na, nb, alg.gates.map fun (fa, fb) => (combine fa Ar, combine fb Br), alg.W⟩

/-- `mont5_alg`: Montgomery's 13 products and the product coefficients `c_0 … c_8`. -/
def mont5 : Alg :=
  let gs : Array Nat := #[0b11111, 0b11101, 0b10111, 0b11011, 0b01101, 0b10110, 0b11000, 0b00011,
    0b10001, 0b10000, 0b01000, 0b00010, 0b00001]
  let w : List (List Nat) := [[12], [7, 11, 12], [2, 5, 7, 8, 9, 12], [0, 1, 3, 6, 8, 9],
    [0, 4, 5, 6, 7, 9, 10, 11, 12], [0, 2, 3, 7, 8, 12], [1, 4, 6, 8, 9, 12], [6, 9, 10], [9]]
  ⟨5, 5, gs.map fun m => (m, m), (w.map fun row => row.foldl (fun acc g => acc ||| (1 <<< g)) 0).toArray⟩

/-! ## The cost search -/

/-- A place (`(kind, poly, e)`): infinity, `x` or `x + 1` (`poly = 0b10`, `0b11`) to the `e`, or an
irreducible's `e`-th power. -/
inductive Place
  | inf (e : Nat)
  | lin (poly e : Nat)
  | irr (poly e : Nat)
  deriving Inhabited, BEq, Repr

inductive FullPlan
  | base | mont5 | split (s m : Nat) | crt (picks : List Place)
  deriving Inhabited

inductive ShortPlan
  | base | full | shortsplit (m : Nat)
  deriving Inhabited

/-- `TOWER_FIELD`. -/
def towerCost (d : Nat) : Option Nat := if d == 6 then some 15 else if d == 8 then some 24 else none

/-- `place_gate_cost`, from the cost tables `fc`, `sc` (indexed by `n`). -/
def placeGateCost (fc sc : Array Nat) : Place → Nat
  | .inf e | .lin _ e => sc[e]!
  | .irr p e =>
    let d := pdeg p
    match towerCost d with
    | some t => if e == 1 then min t fc[d]! else fc[d * e]!
    | none => fc[d * e]!

/-- `crt_search target maxe_lin cap_irr irr_pools` (`pools` sorted by degree): the cheapest
pick of at most one option per group with total degree `≥ target`. The DP table is a list in
Python `dict` order (new degrees appended; an entry is replaced only by a strictly cheaper one). -/
def crtSearch (fc sc : Array Nat) (target maxeLin capIrr : Nat) (pools : List (Nat × List Nat)) :
    Option (Nat × List Place) := Id.run do
  let cost := placeGateCost fc sc
  let mut groups : Array (Array (Nat × Nat × List Place)) := #[]
  for pl in [Place.inf, Place.lin 0b10, Place.lin 0b11] do
    let opts := (Array.range maxeLin).map fun i => (i + 1, sc[i + 1]!, [pl (i + 1)])
    if !opts.isEmpty then groups := groups.push opts
  for (d, pool) in pools do
    match pool with
    | [] => pure ()
    | p0 :: _ =>
      if d == 2 then
        let opts := (Array.range (capIrr / 2)).map fun i =>
          (2 * (i + 1), cost (.irr p0 (i + 1)), [Place.irr p0 (i + 1)])
        if !opts.isEmpty then groups := groups.push opts
      else
        let per := cost (.irr p0 1)
        let maxt := min pool.length (target / d + 1)
        let opts := (Array.range maxt).map fun i =>
          ((i + 1) * d, (i + 1) * per, (pool.take (i + 1)).map (Place.irr · 1))
        if !opts.isEmpty then groups := groups.push opts
  let mut dp : Array (Nat × Nat × List Place) := #[(0, 0, [])]
  for opts in groups do
    let mut ndp := dp
    for (deg0, c0, pk0) in dp do
      for (dd, cc, pks) in opts do
        let nd := min (deg0 + dd) target
        let nc := c0 + cc
        match ndp.findIdx? (·.1 == nd) with
        | none => ndp := ndp.push (nd, nc, pk0 ++ pks)
        | some k => if nc < ndp[k]!.2.1 then ndp := ndp.set! k (nd, nc, pk0 ++ pks)
    dp := ndp
  return (dp.find? (·.1 == target)).map fun (_, c, pk) => (c, pk)

/-- `full_cost`, `short_cost` for `n ≤ N`: costs and plans, bottom-up. -/
def costTables (N : Nat) : Array (Nat × FullPlan) × Array (Nat × ShortPlan) := Id.run do
  let mut full : Array (Nat × FullPlan) := #[(0, .base), (1, .base)]
  let mut short : Array (Nat × ShortPlan) := #[(0, .base), (1, .base)]
  for n in [2:N + 1] do
    let fc := full.map (·.1)
    let sc := short.map (·.1)
    let mut best : Option (Nat × FullPlan) := if n == 5 then some (13, .mont5) else none
    for s in [2:n] do
      let m := (n + s - 1) / s
      let c := fc[s]! * fc[m]!
      if best.all (c < ·.1) then best := some (c, .split s m)
    let pools := (List.range (n - 2)).map fun i => (i + 2, irreducibles (i + 2))
    if let some (c, picks) := crtSearch fc sc (2 * n - 1) (n - 1) (n - 1) pools then
      if best.all (c < ·.1) then best := some (c, .crt picks)
    let bestN := best.getD (0, .base)
    full := full.push bestN
    let mut sbest : Nat × ShortPlan := (bestN.1, .full)
    for m in [(n + 1) / 2:n] do
      let c := full[m]!.1 + 2 * short[n - m]!.1
      if c < sbest.1 then sbest := (c, .shortsplit m)
    short := short.push sbest
  return (full, short)

/-! ## The F₄ tower (`tower_place_alg`) -/

namespace F4

def mul (a b : Nat) : Nat :=
  (#[0, 0, 0, 0, 0, 1, 2, 3, 0, 2, 3, 1, 0, 3, 1, 2] : Array Nat)[4 * a + b]!

def pow (t j : Nat) : Nat := (List.range j).foldl (fun r _ => mul r t) 1

def pmul (A B : Array Nat) : Array Nat := Id.run do
  let mut out := Array.replicate (A.size + B.size - 1) 0
  for i in [0:A.size] do
    if A[i]! != 0 then
      for j in [0:B.size] do
        out := out.modify (i + j) (· ^^^ mul A[i]! B[j]!)
  return out

/-- `A mod Q`, `Q` monic. -/
def pmod (A Q : Array Nat) : Array Nat := Id.run do
  let dq := Q.size - 1
  let mut w := A
  for s in [0:A.size] do
    let i := A.size - 1 - s
    if i ≥ dq then
      let c := w[i]!
      if c != 0 then
        for j in [0:dq + 1] do
          w := w.modify (i - dq + j) (· ^^^ mul c Q[j]!)
  return (w ++ Array.replicate dq 0).extract 0 dq

def peval (P : Array Nat) (t : Nat) : Nat := P.foldr (fun c r => mul r t ^^^ c) 0

/-- `itertools.product(range(4), repeat=m)`, in order. -/
def tuples (m : Nat) : List (Array Nat) :=
  (List.range (4 ^ m)).map fun k => (Array.range m).map fun j => k / 4 ^ (m - 1 - j) % 4

/-- `f4_irreducibles m` (`m ≤ 4`): monic irreducibles of degree `m`, in the script's order. -/
def irreducibles (m : Nat) : List (Array Nat) :=
  let rootless (P : Array Nat) := (List.range 4).all fun u => peval P u != 0
  let quads := ((tuples 2).map (· ++ #[1])).filter rootless
  ((tuples m).map (· ++ #[1])).filter fun P =>
    rootless P && (m != 4 || quads.all fun Q2 => (pmod P Q2).any (· != 0))

/-- `f4_xpow_cols Q count`: `x^j mod Q` for `j < count`. -/
def xpowCols (Q : Array Nat) (count : Nat) : Array (Array Nat) := Id.run do
  let dq := Q.size - 1
  let mut cur : Array Nat := #[1] ++ Array.replicate (dq - 1) 0
  let mut cols := #[]
  for _ in [0:count] do
    cols := cols.push cur
    cur := pmod (#[0] ++ cur) Q
  return cols

/-- `f4_matinv` (Gauss–Jordan; the inverse of an invertible matrix). -/
def matinv (M : Array (Array Nat)) : Array (Array Nat) := Id.run do
  let n := M.size
  let inv : Array Nat := #[0, 1, 3, 2]
  let mut A := (Array.range n).map fun i =>
    M[i]! ++ (Array.range n).map fun j => if j == i then 1 else 0
  for c in [0:n] do
    let piv := ((List.range n).find? fun i => i ≥ c && A[i]![c]! != 0).getD c
    let (ac, ap) := (A[c]!, A[piv]!)
    A := (A.set! c ap).set! piv ac
    let iv := inv[A[c]![c]!]!
    A := A.set! c (A[c]!.map (mul iv ·))
    for i in [0:n] do
      if i != c && A[i]![c]! != 0 then
        let f := A[i]![c]!
        A := A.set! i ((Array.range (2 * n)).map fun j => A[i]![j]! ^^^ mul f A[c]![j]!)
  return A.map (·.extract n (2 * n))

/-- `_f4_full_product_alg m`: the F₄-linear forms of the F₄-multiplications and the `(2m−1)`-row
recombination matrix. -/
def fullProduct (m : Nat) : Array (Array Nat) × Array (Array Nat) := Id.run do
  let mut gates4 : Array (Array Nat) := #[]
  let mut ev : Array (Array Nat) := #[]
  let mut R4 : Array (List (Nat × Nat)) := #[]
  let npts := if m == 2 then 2 else 4
  for t in [0:npts] do
    R4 := R4.push [(gates4.size, 1)]
    gates4 := gates4.push ((Array.range m).map (pow t ·))
    ev := ev.push ((Array.range (2 * m - 1)).map (pow t ·))
  R4 := R4.push [(gates4.size, 1)]
  gates4 := gates4.push (Array.replicate (m - 1) 0 ++ #[1])
  ev := ev.push (Array.replicate (2 * m - 2) 0 ++ #[1])
  if m == 4 then
    let Q2 := (irreducibles 2).headD #[]
    let beta := Q2[0]!
    let alpha := Q2[1]!
    let colsIn := xpowCols Q2 m
    let r0 := colsIn.map (·[0]!)
    let r1 := colsIn.map (·[1]!)
    let ga := gates4.size
    gates4 := gates4 ++ #[r0, r1, (Array.range m).map fun i => r0[i]! ^^^ r1[i]!]
    let colsOut := xpowCols Q2 (2 * m - 1)
    ev := ev ++ #[colsOut.map (·[0]!), colsOut.map (·[1]!)]
    R4 := R4 ++ #[[(ga, 1), (ga + 1, beta)], [(ga, 1), (ga + 1, 1 ^^^ alpha), (ga + 2, 1)]]
  let Inv := matinv ev
  let ng := gates4.size
  let mut W4 : Array (Array Nat) := Array.replicate (2 * m - 1) (Array.replicate ng 0)
  for k in [0:2 * m - 1] do
    for j in [0:R4.size] do
      let c := Inv[k]![j]!
      if c != 0 then
        for (g, coeff) in R4[j]! do
          W4 := W4.modify k (·.modify g (· ^^^ mul c coeff))
  return (gates4, W4)

end F4

/-- `tower_place_alg q na nb` (`deg q ∈ {6, 8}`): the residue of the product modulo the irreducible
`q`, through F₂[y]/q ≅ F₄[x]/Q. -/
def towerPlace (q na nb : Nat) : Alg × Array Nat := Id.run do
  let d := pdeg q
  let m := d / 2
  let Q := (F4.irreducibles m).headD #[]
  let (gates4, W4) := F4.fullProduct m
  let RQ := F4.xpowCols Q (2 * m - 1)
  let ng4 := gates4.size
  let mut W4m : Array (Array Nat) := Array.replicate m (Array.replicate ng4 0)
  for k in [0:m] do
    for j in [0:2 * m - 1] do
      let c := RQ[j]![k]!
      if c != 0 then
        for g in [0:ng4] do
          W4m := W4m.modify k (·.modify g (· ^^^ F4.mul c W4[j]![g]!))
  let one : Array Nat := #[1] ++ Array.replicate (m - 1) 0
  let tmul (a b : Array Nat) : Array Nat := F4.pmod (F4.pmul a b) Q
  let isRoot (cand : Array Nat) : Bool := Id.run do
    let mut acc : Array Nat := Array.replicate m 0
    for s in [0:d + 1] do
      acc := tmul acc cand
      if q.testBit (d - s) then acc := acc.modify 0 (· ^^^ 1)
    return acc.all (· == 0)
  let rho := ((F4.tuples m).find? isRoot).getD one
  let mut cols : Array Nat := #[]
  let mut p := one
  for _ in [0:d] do
    cols := cols.push ((List.range m).foldl (fun acc j => acc ||| (p[j]! <<< (2 * j))) 0)
    p := tmul p rho
  let Mrows : Array Nat := (Array.range d).map fun r =>
    (List.range d).foldl (fun acc i => if cols[i]!.testBit r then acc ||| (1 <<< i) else acc) 0
  let Minv := leftInverse Mrows d
  let trowA := (Array.range d).map fun r => combine Mrows[r]! (reductionRows q na)
  let trowB := (Array.range d).map fun r => combine Mrows[r]! (reductionRows q nb)
  let formBits (L : Array Nat) (trow : Array Nat) : Nat × Nat := Id.run do
    let mut p := 0
    let mut r := 0
    for j in [0:L.size] do
      let c := L[j]!
      let pj := trow[2 * j]!
      let rj := trow[2 * j + 1]!
      if c &&& 1 != 0 then
        p := p ^^^ pj
        r := r ^^^ rj
      if c &&& 2 != 0 then
        p := p ^^^ rj
        r := r ^^^ pj ^^^ rj
    return (p, r)
  let mut gates : Array (Nat × Nat) := #[]
  let mut comp : Array (Nat × Nat) := #[]
  for L in gates4 do
    let (pa, ra) := formBits L trowA
    let (pb, rb) := formBits L trowB
    let b := gates.size
    gates := gates ++ #[(pa, pb), (ra, rb), (pa ^^^ ra, pb ^^^ rb)]
    comp := comp.push ((1 <<< b) ||| (1 <<< (b + 1)), (1 <<< b) ||| (1 <<< (b + 2)))
  let mut towout : Array Nat := Array.replicate d 0
  for k in [0:m] do
    let mut o0 := 0
    let mut o1 := 0
    for g in [0:ng4] do
      let c := W4m[k]![g]!
      let (G0, G1) := comp[g]!
      if c &&& 1 != 0 then
        o0 := o0 ^^^ G0
        o1 := o1 ^^^ G1
      if c &&& 2 != 0 then
        o0 := o0 ^^^ G1
        o1 := o1 ^^^ G0 ^^^ G1
    towout := (towout.set! (2 * k) o0).set! (2 * k + 1) o1
  return (⟨na, nb, gates, (Array.range d).map fun r => combine Minv[r]! towout⟩,
    reductionRows q (na + nb - 1))

/-! ## The algorithms of the plans -/

/-- `place_alg pk na nb`, given `full_alg`, `short_alg` for small sizes and `full_cost`: the
place's algorithm and the rows of its residue map on the `(na + nb − 1)`-coefficient product. -/
def placeAlg (fa sa : Array Alg) (fc : Array Nat) (pk : Place) (na nb : Nat) : Alg × Array Nat :=
  let N2 := na + nb - 1
  match pk with
  | .inf e =>
    let ra := (Array.range e).map fun i => 1 <<< (na - 1 - i)
    let rb := (Array.range e).map fun i => 1 <<< (nb - 1 - i)
    (precompose sa[e]! ra rb na nb, (Array.range e).map fun i => 1 <<< (N2 - 1 - i))
  | .lin poly e =>
    let q := ppow poly e
    let Ra := reductionRows q na
    let Rb := reductionRows q nb
    let Rev := reductionRows q N2
    if poly == 0b10 then (precompose sa[e]! Ra Rb na nb, Rev)
    else
      let P := pascalRows e
      let sub (R : Array Nat) := (Array.range e).map fun i => combine P[i]! R
      (precompose sa[e]! (sub Ra) (sub Rb) na nb, sub Rev)
  | .irr poly e =>
    let dp := pdeg poly
    if e == 1 && (towerCost dp).any (· < fc[dp]!) then towerPlace poly na nb
    else
      let q := ppow poly e
      let d := pdeg q
      let alg := precompose fa[d]! (reductionRows q na) (reductionRows q nb) na nb
      let Rout := reductionRows q (2 * d - 1)
      (⟨na, nb, alg.gates, (Array.range d).map fun i => combine Rout[i]! alg.W⟩,
        reductionRows q N2)

/-- The places' algorithms side by side: gates, the residue masks over all gates, and the
evaluation rows. -/
def placesAlg (fa sa : Array Alg) (fc : Array Nat) (picks : List Place) (na nb : Nat) :
    Array (Nat × Nat) × Array Nat × Array Nat := Id.run do
  let mut gates : Array (Nat × Nat) := #[]
  let mut resmasks : Array Nat := #[]
  let mut evrows : Array Nat := #[]
  for pk in picks do
    let (palg, ev) := placeAlg fa sa fc pk na nb
    let off := gates.size
    gates := gates ++ palg.gates
    resmasks := resmasks ++ palg.W.map (· <<< off)
    evrows := evrows ++ ev
  return (gates, resmasks, evrows)

/-- `full_alg` of a split plan: `full(s)` over `full(m)` blocks of the `n` coefficients. -/
def splitAlg (OA IA : Alg) (n s m : Nat) : Alg := Id.run do
  let ngi := IA.gates.size
  let spread (x : Nat) : Array Nat := (Array.range m).map fun i =>
    (bits x).foldl (fun acc t => if t * m + i < n then acc ||| (1 <<< (t * m + i)) else acc) 0
  let mut gates : Array (Nat × Nat) := #[]
  for (Fo, Go) in OA.gates do
    let Ar := spread Fo
    let Br := spread Go
    for (fi, gi) in IA.gates do
      gates := gates.push (combine fi Ar, combine gi Br)
  let W := (Array.range (2 * n - 1)).map fun q =>
    (List.range (2 * s - 1)).foldl (fun row r =>
      if r * m ≤ q && q - r * m ≤ 2 * m - 2 then
        (bits OA.W[r]!).foldl (fun row o => row ^^^ (IA.W[q - r * m]! <<< (o * ngi))) row
      else row) 0
  return ⟨n, n, gates, W⟩

/-- `short_alg` of a `shortsplit m` plan. -/
def shortSplitAlg (FM S : Alg) (n m : Nat) : Alg :=
  let lo := (Array.range m).map (1 <<< ·)
  let G1 := precompose FM lo lo n n
  let lo2 := (Array.range (n - m)).map (1 <<< ·)
  let hi2 := (Array.range (n - m)).map fun i => 1 <<< (m + i)
  let G2 := precompose S lo2 hi2 n n
  let G3 := precompose S hi2 lo2 n n
  let o2 := G1.gates.size
  let o3 := o2 + G2.gates.size
  let W := (Array.range n).map fun j =>
    let row := if j ≤ 2 * m - 2 then G1.W[j]! else 0
    if j ≥ m then row ^^^ (G2.W[j - m]! <<< o2) ^^^ (G3.W[j - m]! <<< o3) else row
  ⟨n, n, G1.gates ++ G2.gates ++ G3.gates, W⟩

/-- `full_alg n`, `short_alg n` for `n ≤ N`, bottom-up. -/
def algTables (N : Nat) : Array Alg × Array Alg := Id.run do
  let (full, short) := costTables N
  let fc := full.map (·.1)
  let mut fa : Array Alg := #[Alg.base, Alg.base]
  let mut sa : Array Alg := #[Alg.base, Alg.base]
  for n in [2:N + 1] do
    let alg : Alg := match full[n]!.2 with
      | .base => Alg.base
      | .mont5 => mont5
      | .split s m => splitAlg fa[s]! fa[m]! n s m
      | .crt picks =>
        let (gates, resmasks, evrows) := placesAlg fa sa fc picks n n
        let X := leftInverse evrows (2 * n - 1)
        ⟨n, n, gates, (Array.range (2 * n - 1)).map fun q => combine X[q]! resmasks⟩
    fa := fa.push alg
    let salg : Alg := match short[n]!.2 with
      | .base => Alg.base
      | .full => ⟨n, n, alg.gates, alg.W.extract 0 n⟩
      | .shortsplit m => shortSplitAlg fa[m]! sa[n - m]! n m
    sa := sa.push salg
  return (fa, sa)

/-! ## The `128f` table set (`run_set`, `build_tables`, `prune`) -/

/-- `(λ, τ, w)` of `128f`, the search bounds (`--maxd`, `--maxe`), and FAEST's `P_128`. -/
def lam : Nat := 128
def tau : Nat := 17
def wgrind : Nat := 8
def maxd : Nat := 10
def maxe : Nat := 10
def fieldModulus : Nat := 2 ^ 128 + 2 ^ 7 + 2 ^ 2 + 2 + 1

/-- `faest_tree_spec`: `(degree, count)`, larger degree first. -/
def treeSpec : List (Nat × Nat) :=
  let n := lam - wgrind
  let d1 := n / tau + 1
  let tau1 := n % tau
  (if tau1 != 0 then [(d1, tau1)] else []) ++ [(d1 - 1, tau - tau1)]

/-- The tree moduli: the smallest irreducibles of each tree degree. -/
def treeModuli : Array Nat := (treeSpec.flatMap fun (d, c) => (irreducibles d).take c).toArray

/-- `crt_lift_cols`: the CRT lifts of the tree residue basis bits. -/
def crtLiftCols (ms : Array Nat) : Array Nat := Id.run do
  let Mtree := ms.foldl pmul 1
  let mut cols := #[]
  for M in ms do
    let Q := pdiv Mtree M
    let E := pmulmod Q (pinv (pmod Q M) M) Mtree
    for b in [0:pdeg M] do
      cols := cols.push (pmulmod E (1 <<< b) Mtree)
  return cols

/-- `prune F G W_gate`: drop zero gates, merge duplicates, drop unused gates. -/
def prune (F G Wg : Array Nat) : Array Nat × Array Nat × Array Nat := Id.run do
  let ng := F.size
  let live (g : Nat) : Bool := F[g]! != 0 && G[g]! != 0
  let canon (g : Nat) : Nat :=
    ((List.range ng).find? fun h => live h && F[h]! == F[g]! && G[h]! == G[g]!).getD g
  let Wg1 := Wg.map fun row =>
    (bits row).foldl (fun nr g => if live g then nr ^^^ (1 <<< canon g) else nr) 0
  let used := Wg1.foldl (· ||| ·) 0
  let mut newidx : Array Nat := Array.replicate ng 0
  let mut F2 := #[]
  let mut G2 := #[]
  for g in [0:ng] do
    if used.testBit g then
      newidx := newidx.set! g F2.size
      F2 := F2.push F[g]!
      G2 := G2.push G[g]!
  return (F2, G2, Wg1.map fun row => (bits row).foldl (fun nr g => nr ||| (1 <<< newidx[g]!)) 0)

/-- The portfolio of `run_set` and `F`, `G`, `W_tree`, `W_gate` after `prune`. -/
structure Tables where
  picks : List Place
  F : Array Nat
  G : Array Nat
  wTree : Array Nat
  wGate : Array Nat

/-- `run_set` for `128f`: tree moduli, portfolio search, `build_tables`, `prune`. -/
def generate : Tables := Id.run do
  let ms := treeModuli
  let na := lam
  let nb := lam - wgrind
  let ntree := ms.foldl (fun acc M => acc + pdeg M) 0
  let N2 := na + nb - 1
  let (full, short) := costTables maxd
  let fc := full.map (·.1)
  let sc := short.map (·.1)
  let pools := (List.range (maxd - 1)).map fun i =>
    (i + 2, (irreducibles (i + 2)).filter fun q => !ms.contains q)
  let picks := ((crtSearch fc sc (N2 - ntree) maxe maxd pools).map (·.2)).getD []
  let (fa, sa) := algTables maxd
  let (gates, resmasks, ev) := placesAlg fa sa fc picks na nb
  let evrows := ms.foldl (fun acc M => acc ++ reductionRows M N2) #[] ++ ev
  let X := leftInverse evrows N2
  let Red := reductionRows fieldModulus N2
  let mut Wt : Array Nat := Array.replicate lam 0
  let mut Wg : Array Nat := Array.replicate lam 0
  for r in [0:lam] do
    for idx in bits (combine Red[r]! X) do
      if idx < ntree then Wt := Wt.modify r (· ||| (1 <<< idx))
      else Wg := Wg.modify r (· ^^^ resmasks[idx - ntree]!)
  let cols := crtLiftCols ms
  let F := gates.map (·.1)
  let G := gates.map fun (_, fb) =>
    (List.range nb).foldl (fun acc j => if parity (fb &&& cols[j]!) then acc ||| (1 <<< j) else acc) 0
  let (F, G, Wg') := prune F G Wg
  return ⟨picks, F, G, Wt, Wg'⟩

/-- The regenerated tables equal `CrtData`'s (tree moduli, field modulus, `F`, `G`, `W_tree`,
`W_gate`). -/
def regenOk (T : Tables) : Bool :=
  treeModuli == moduli && fieldModulus == hexNat CrtData.modulusHex &&
    T.F == CrtGen.F && T.G == CrtGen.G && T.wTree == CrtGen.wTree && T.wGate == CrtGen.wGate

end VoleMole.Verifier.CrtSearch
