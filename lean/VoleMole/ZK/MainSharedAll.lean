import VoleMole.ZK.MainShared23
import VoleMole.ZK.SharedH3

/-!
# The joint hop on `main` with one shared `H₃` (`lean/docs/zk.md` §4.2)

`main_shared23_le` (`ZK/MainShared23.lean`) replaces four `main`-layout proofs by simulated ones
when they share the `H₅` table, the cipher and the `H₂³` table; each proof keeps its own `H₃`
slice. Here the four proofs also **share `H₃`**, as in the scheme: one table `T : H3T` with a
column at every prefix (`Pre`, `ZK/SharedH3.lean`), and the real proof with statement and witness
`y` reads the column at its prefix `wPrefix ‖ μ₁` (`preOf`; `prove_recOne` in
`ZK/SharedH3One.lean`: the executable prover with one `H₃` is the prover with this column as
its slice). The adversary sees `T` and reads it at `q₃` points `(prefix, ρ)` (`RdH`); it does not
see the per-proof slices of the hybrid tape (`RdH.h3₁` …: events ignore them).

## The reduction (`realAll_close`, `simAll_eq`)

The joint hop is not redone. An event `F` of the view and of `T` is turned into an event of the
slice game, `F' T₀ v = F v (tabOf T₀ v)`: `tabOf` writes the four slices of the view into the
columns at the four proofs' prefixes of an independent table `T₀` (the earliest outermost). The
prefixes are functions of the view (of the secret and the earlier outputs: the statements of a
`MainChain.Game`), so `F'` is an event of the view in the sense of `main_shared23_le`, and it
reads slice `j` at the points `(prefix_j, ρ)` at which `F` reads `T` (`rdH_tabOf`).

* **Overwriting columns keeps `T` uniform** (`pr_updO_lens`, `pr_upd4`): writing the tape's slice
  `g_j` (unused by the shared game) into the column at prefix `k_j` is measure-preserving as long
  as `k_j` does not depend on `g_j`. The prefix of proof `j` depends on the earlier proofs'
  outputs, hence on `g₁ … g_{j-1}`, not on `g_j … g₄`; so the four columns are written in game
  order.
* **Real side**: after the overwriting, the shared game's proof `j` reads `g_j` and runs as the
  slice game's proof `j`, unless two proofs have the same prefix (`DistV`: then a later proof
  reads the earlier one's slice). So `|Pr_shared[F] − Pr_slice[F']| ≤ Pr[two prefixes coincide]`
  (`realAll_close`), a term of the secret for the games of Moussaka and Ratatouille.
* **Simulated side**: the simulators read no `H₃`, so the overwriting is exact
  (`simAll_eq`), also for the bad event `bstar` (`simAll_bstar_eq`).

This is a reduction that knows the secret: `F'` computes the prefixes, which contain the Clients'
openings. It is sound here because `main_shared23_le` holds for every event of the view, the
secret included (its terms are the slice reads `q₃·2⁻¹²⁸`, which hold for any reader, and `bstar`,
whose read set is `F`'s), and because the statements of the game do not read the tables.

## The result (`main_sharedAll_le`)

    |Pr[all real; F] − Pr[all simulated; F]| ≤ 15·(εS(q₃, q_E + 8·4607) + Δ23)
        + 15·Pr[all simulated; bstar] + Pr[two of the real proofs' prefixes coincide]

for `F` and its `H₅` read set `R5` with consistent reads (`RdH`): `T` at `q₃` points, the cipher
at `q_E` keys, `H₅` at `R5`.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy
  VoleMole.ZK.IC
open VoleMole.Privacy.MainChain

attribute [local instance] decEqW128
attribute [local irreducible] simulate realRO progRO realKeys5 realKeysE progKeys5 progKeysE

/-! ## One `H₃` table, and overwriting its columns -/

/-- **One `H₃`**: its column at every prefix (`ρ ↦ H₃(prefix ‖ ρ ‖ 3)`). -/
abbrev H3T := Pre → Tab3

/-- The table with the column at `k` (if any) overwritten by `g`. -/
def updO (T : H3T) (k : Option Pre) (g : Tab3) : H3T :=
  match k with
  | some k => Function.update T k g
  | none => T

lemma updO_apply (T : H3T) (k : Option Pre) (g : Tab3) (k' : Pre) :
    updO T k g k' = if k = some k' then g else T k' := by
  cases k with
  | none => simp [updO]
  | some k =>
    by_cases h : k' = k
    · subst h; simp [updO]
    · simp [updO, Function.update_of_ne h, Ne.symm h]

/-- The exchange of a tape's slice with the column at `k x`. -/
def swapL {X : Type*} (get : X → Tab3) (set : X → Tab3 → X) (k : X → Option Pre)
    (z : X × H3T) : X × H3T :=
  match k z.1 with
  | some k₀ => (set z.1 (z.2 k₀), Function.update z.2 k₀ (get z.1))
  | none => z

/-- **Overwriting a column with a tape slice that nothing else reads keeps the table uniform**:
for a lens `get`/`set` on the tape, a column `k x` that does not depend on the slice, and an
event that does not read the slice. -/
theorem pr_updO_lens {X : Type*} [Fintype X] (get : X → Tab3) (set : X → Tab3 → X)
    (gs : ∀ x g, get (set x g) = g) (sg : ∀ x, set x (get x) = x)
    (ss : ∀ x g g', set (set x g) g' = set x g')
    (k : X → Option Pre) (hk : ∀ x g, k (set x g) = k x)
    (Ψ : X → H3T → Prop) (hΨ : ∀ x g T, Ψ (set x g) T ↔ Ψ x T) :
    pr (X × H3T) (fun z => Ψ z.1 (updO z.2 (k z.1) (get z.1))) = pr (X × H3T) (fun z => Ψ z.1 z.2) := by
  have hinv : Function.Involutive (swapL get set k) := by
    rintro ⟨x, T⟩
    unfold swapL
    rcases hx : k x with _ | k₀
    · simp only [hx]
    · simp only [hx, hk, gs, Function.update_self, Function.update_idem, ss,
        Function.update_eq_self, sg]
  conv_rhs => rw [← pr_equiv hinv.toPerm]
  refine pr_congr fun ⟨x, T⟩ => ?_
  show Ψ x (updO T (k x) (get x)) ↔ Ψ (swapL get set k (x, T)).1 (swapL get set k (x, T)).2
  unfold swapL
  rcases hx : k x with _ | k₀
  · simp only [updO]
  · simp only [updO]
    exact (hΨ _ _ _).symm

/-! ## The four slices of the hybrid tape -/

section Tape

variable {S : Type} {p₁ p₂ p₃ p₄ : Params}

/-- Slot `j`'s `H₃` slice on the tape, and the tape with it replaced. -/
def g3T₁ (x : GTape S p₁ p₂ p₃ p₄) : Tab3 := x.2.2.1.2.1
def g3T₂ (x : GTape S p₁ p₂ p₃ p₄) : Tab3 := x.2.2.2.1.2.1
def g3T₃ (x : GTape S p₁ p₂ p₃ p₄) : Tab3 := x.2.2.2.2.1.2.1
def g3T₄ (x : GTape S p₁ p₂ p₃ p₄) : Tab3 := x.2.2.2.2.2.2.1
def s3T₁ (x : GTape S p₁ p₂ p₃ p₄) (g : Tab3) : GTape S p₁ p₂ p₃ p₄ :=
  (x.1, x.2.1, ((x.2.2.1.1, (g, x.2.2.1.2.2)), x.2.2.2))
def s3T₂ (x : GTape S p₁ p₂ p₃ p₄) (g : Tab3) : GTape S p₁ p₂ p₃ p₄ :=
  (x.1, x.2.1, x.2.2.1, ((x.2.2.2.1.1, (g, x.2.2.2.1.2.2)), x.2.2.2.2))
def s3T₃ (x : GTape S p₁ p₂ p₃ p₄) (g : Tab3) : GTape S p₁ p₂ p₃ p₄ :=
  (x.1, x.2.1, x.2.2.1, x.2.2.2.1, ((x.2.2.2.2.1.1, (g, x.2.2.2.2.1.2.2)), x.2.2.2.2.2))
def s3T₄ (x : GTape S p₁ p₂ p₃ p₄) (g : Tab3) : GTape S p₁ p₂ p₃ p₄ :=
  (x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, (x.2.2.2.2.2.1, (g, x.2.2.2.2.2.2.2)))

variable [Fintype S]

/-- **The four columns written in game order keep `T` uniform**: column `k_j` gets slice `g_j`
(the earliest outermost), `k_j` depends on no slice `g_m` with `m ≥ j`, and the event reads no
slice. -/
theorem pr_upd4 (k₁ k₂ k₃ k₄ : GTape S p₁ p₂ p₃ p₄ → Option Pre) (Φ : GTape S p₁ p₂ p₃ p₄ → H3T → Prop)
    (h₁ : ∀ x g T, Φ (s3T₁ x g) T ↔ Φ x T) (h₂ : ∀ x g T, Φ (s3T₂ x g) T ↔ Φ x T)
    (h₃ : ∀ x g T, Φ (s3T₃ x g) T ↔ Φ x T) (h₄ : ∀ x g T, Φ (s3T₄ x g) T ↔ Φ x T)
    (k11 : ∀ x g, k₁ (s3T₁ x g) = k₁ x) (k12 : ∀ x g, k₁ (s3T₂ x g) = k₁ x)
    (k13 : ∀ x g, k₁ (s3T₃ x g) = k₁ x) (k14 : ∀ x g, k₁ (s3T₄ x g) = k₁ x)
    (k22 : ∀ x g, k₂ (s3T₂ x g) = k₂ x) (k23 : ∀ x g, k₂ (s3T₃ x g) = k₂ x)
    (k24 : ∀ x g, k₂ (s3T₄ x g) = k₂ x) (k33 : ∀ x g, k₃ (s3T₃ x g) = k₃ x)
    (k34 : ∀ x g, k₃ (s3T₄ x g) = k₃ x) (k44 : ∀ x g, k₄ (s3T₄ x g) = k₄ x) :
    pr (GTape S p₁ p₂ p₃ p₄ × H3T) (fun z => Φ z.1 (updO (updO (updO (updO z.2 (k₄ z.1) (g3T₄ z.1))
      (k₃ z.1) (g3T₃ z.1)) (k₂ z.1) (g3T₂ z.1)) (k₁ z.1) (g3T₁ z.1))) =
      pr (GTape S p₁ p₂ p₃ p₄ × H3T) (fun z => Φ z.1 z.2) := by
  have s1 := pr_updO_lens g3T₁ s3T₁ (fun _ _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) k₁ k11 Φ h₁
  have s2 := pr_updO_lens g3T₂ s3T₂ (fun _ _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) k₂ k22
    (fun x T => Φ x (updO T (k₁ x) (g3T₁ x))) (fun x g T => by
      simp only [k12]; exact h₂ x g _)
  have s3 := pr_updO_lens g3T₃ s3T₃ (fun _ _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) k₃ k33
    (fun x T => Φ x (updO (updO T (k₂ x) (g3T₂ x)) (k₁ x) (g3T₁ x))) (fun x g T => by
      simp only [k13, k23]; exact h₃ x g _)
  have s4 := pr_updO_lens g3T₄ s3T₄ (fun _ _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) k₄ k44
    (fun x T => Φ x (updO (updO (updO T (k₃ x) (g3T₃ x)) (k₂ x) (g3T₂ x)) (k₁ x) (g3T₁ x)))
    (fun x g T => by simp only [k14, k24, k34]; exact h₄ x g _)
  rw [s4, s3, s2, s1]

end Tape

/-! ## The real prover with one `H₃` -/

section Shared

variable (Hb : Hashes)

/-- **The prefix of a proof**: `wPrefix ‖ μ₁` for the statement and witness `y` with parameters
`p` (the bytes the executable prover hashes before `ρ ‖ 3`, `prove_recOne`). -/
noncomputable def preOf (p : Params) (y : SW) : Pre :=
  preKey (y.2.extract 0 p.witnessBytes ++ (withP y.1 p).mu1 Hb)

/-- **The real prover reading one `H₃`**: its slice is the column of `T` at its prefix. Its tape
slice `g` is not read; it is the behaviour's `g3`, which the events of the shared game ignore. -/
noncomputable def realSBT (p : Params) (ρ : Bytes 16) (g : Tab3) (T : H3T) : SB p where
  run y t := realRO p Hb (withP y.1 p) y.2 ρ (T (preOf Hb p y)) t
  pg _ _ G2 := G2
  g3 := g
  r5 y t := match y with
    | some y => realKeys5 p Hb (withP y.1 p) y.2 (ba ρ) (T (preOf Hb p y)) t
    | none => ∅
  rE y t := match y with
    | some y => realKeysE p Hb (withP y.1 p) y.2 (ba ρ) (T (preOf Hb p y)) t
    | none => ∅
  q5 _ _ := ∅
  qE _ _ := ∅

end Shared

/-! ## The prefixes of a view, and the table built from its slices -/

section Keys

variable {S : Type} {p₁ p₂ p₃ p₄ : Params} (Hb : Hashes) (G : Game S Out SW SW SW SW)

/-- The prefixes of the four proofs of a view (none if the slot proves nothing). -/
noncomputable def kv₁ (v : GView S p₁ p₂ p₃ p₄) : Option Pre := (yv₁ G v).map (preOf Hb p₁)
noncomputable def kv₂ (v : GView S p₁ p₂ p₃ p₄) : Option Pre := (yv₂ G v).map (preOf Hb p₂)
noncomputable def kv₃ (v : GView S p₁ p₂ p₃ p₄) : Option Pre := (yv₃ G v).map (preOf Hb p₃)
noncomputable def kv₄ (v : GView S p₁ p₂ p₃ p₄) : Option Pre := (yv₄ G v).map (preOf Hb p₄)

/-- **The table of a slice view**: `T₀` with the column at each proof's prefix overwritten by
that proof's slice, the earliest outermost. -/
noncomputable def tabOf (T₀ : H3T) (v : GView S p₁ p₂ p₃ p₄) : H3T :=
  updO (updO (updO (updO T₀ (kv₄ Hb G v) v.v₄.1) (kv₃ Hb G v) v.v₃.1) (kv₂ Hb G v) v.v₂.1)
    (kv₁ Hb G v) v.v₁.1

/-- Two optional prefixes that are not the same prefix. -/
def DistO (a b : Option Pre) : Prop := ∀ k ∈ a, ∀ k' ∈ b, k ≠ k'

/-- **The four proofs' prefixes are pairwise different.** -/
def DistV (v : GView S p₁ p₂ p₃ p₄) : Prop :=
  DistO (kv₁ Hb G v) (kv₂ Hb G v) ∧ DistO (kv₁ Hb G v) (kv₃ Hb G v) ∧
    DistO (kv₁ Hb G v) (kv₄ Hb G v) ∧ DistO (kv₂ Hb G v) (kv₃ Hb G v) ∧
    DistO (kv₂ Hb G v) (kv₄ Hb G v) ∧ DistO (kv₃ Hb G v) (kv₄ Hb G v)

lemma ne_of_distO {a b : Option Pre} {k : Pre} (h : DistO a b) (hb : b = some k) : a ≠ some k := by
  intro ha
  exact h k ha k hb rfl

lemma ne_of_distO' {a b : Option Pre} {k : Pre} (h : DistO a b) (ha : a = some k) : b ≠ some k := by
  intro hb
  exact h k ha k hb rfl

variable {Hb G}

lemma tabOf_at₁ {T₀ : H3T} {v : GView S p₁ p₂ p₃ p₄} {k : Pre} (hk : kv₁ Hb G v = some k) :
    tabOf Hb G T₀ v k = v.v₁.1 := by
  simp only [tabOf, updO_apply, hk, ite_true]

lemma tabOf_at₂ {T₀ : H3T} {v : GView S p₁ p₂ p₃ p₄} (hD : DistV Hb G v) {k : Pre}
    (hk : kv₂ Hb G v = some k) : tabOf Hb G T₀ v k = v.v₂.1 := by
  simp only [tabOf, updO_apply, hk, ite_true, ite_false, ne_of_distO hD.1 hk]

lemma tabOf_at₃ {T₀ : H3T} {v : GView S p₁ p₂ p₃ p₄} (hD : DistV Hb G v) {k : Pre}
    (hk : kv₃ Hb G v = some k) : tabOf Hb G T₀ v k = v.v₃.1 := by
  simp only [tabOf, updO_apply, hk, ite_true, ite_false, ne_of_distO hD.2.1 hk,
    ne_of_distO hD.2.2.2.1 hk]

lemma tabOf_at₄ {T₀ : H3T} {v : GView S p₁ p₂ p₃ p₄} (hD : DistV Hb G v) {k : Pre}
    (hk : kv₄ Hb G v = some k) : tabOf Hb G T₀ v k = v.v₄.1 := by
  simp only [tabOf, updO_apply, hk, ite_true, ite_false, ne_of_distO hD.2.2.1 hk,
    ne_of_distO hD.2.2.2.2.1 hk, ne_of_distO hD.2.2.2.2.2 hk]

/-! ## Events of the view and of the one `H₃` -/

/-- **`f` reads the tables of a view and the one `H₃` within explicit sets**: the `H₅` table only
at `R5`, the cipher at `qE` keys, `H₃` at `q3` points `(prefix, ρ)`; it does not read the
per-proof slices of the view (which the shared game does not have). -/
structure RdH {X : Sort*} (f : GView S p₁ p₂ p₃ p₄ → H3T → X)
    (R5 : GView S p₁ p₂ p₃ p₄ → H3T → Finset (Bytes 37)) (q3 qE : ℕ) : Prop where
  h5 : ∀ v T (G5 : Tab5F), (∀ k ∈ R5 v T, v.u.1 k = G5 k) → f (v.withU (G5, v.u.2)) T = f v T
  hE : ∃ Q : GView S p₁ p₂ p₃ p₄ → H3T → Finset Blk, (∀ v T, (Q v T).card ≤ qE) ∧
    ∀ v T (E : Cipher), (∀ k ∈ Q v T, v.u.2 k = E k) → f (v.withU (v.u.1, E)) T = f v T
  hT : ∃ Q : GView S p₁ p₂ p₃ p₄ → H3T → Finset (Pre × Bytes 16), (∀ v T, (Q v T).card ≤ q3) ∧
    ∀ v T T', (∀ k ∈ Q v T, T k.1 k.2 = T' k.1 k.2) → f v T' = f v T
  i₁ : ∀ v T G3, f (v.with3₁ G3) T = f v T
  i₂ : ∀ v T G3, f (v.with3₂ G3) T = f v T
  i₃ : ∀ v T G3, f (v.with3₃ G3) T = f v T
  i₄ : ∀ v T G3, f (v.with3₄ G3) T = f v T

lemma tabOf_with3₁ (T₀ : H3T) (v : GView S p₁ p₂ p₃ p₄) (G3 : Tab3) (k : Pre) (ρ : Bytes 16)
    (h : kv₁ Hb G v = some k → v.v₁.1 ρ = G3 ρ) :
    tabOf Hb G T₀ v k ρ = tabOf Hb G T₀ (v.with3₁ G3) k ρ := by
  show (updO (updO (updO (updO T₀ (kv₄ Hb G v) v.v₄.1) (kv₃ Hb G v) v.v₃.1) (kv₂ Hb G v) v.v₂.1)
    (kv₁ Hb G v) v.v₁.1) k ρ = (updO (updO (updO (updO T₀ (kv₄ Hb G v) v.v₄.1) (kv₃ Hb G v)
      v.v₃.1) (kv₂ Hb G v) v.v₂.1) (kv₁ Hb G v) G3) k ρ
  simp only [updO_apply]
  split_ifs with h1 <;> simp_all

lemma tabOf_with3₂ (T₀ : H3T) (v : GView S p₁ p₂ p₃ p₄) (G3 : Tab3) (k : Pre) (ρ : Bytes 16)
    (h : kv₂ Hb G v = some k → v.v₂.1 ρ = G3 ρ) :
    tabOf Hb G T₀ v k ρ = tabOf Hb G T₀ (v.with3₂ G3) k ρ := by
  show (updO (updO (updO (updO T₀ (kv₄ Hb G v) v.v₄.1) (kv₃ Hb G v) v.v₃.1) (kv₂ Hb G v) v.v₂.1)
    (kv₁ Hb G v) v.v₁.1) k ρ = (updO (updO (updO (updO T₀ (kv₄ Hb G v) v.v₄.1) (kv₃ Hb G v)
      v.v₃.1) (kv₂ Hb G v) G3) (kv₁ Hb G v) v.v₁.1) k ρ
  simp only [updO_apply]
  split_ifs <;> simp_all

lemma tabOf_with3₃ (T₀ : H3T) (v : GView S p₁ p₂ p₃ p₄) (G3 : Tab3) (k : Pre) (ρ : Bytes 16)
    (h : kv₃ Hb G v = some k → v.v₃.1 ρ = G3 ρ) :
    tabOf Hb G T₀ v k ρ = tabOf Hb G T₀ (v.with3₃ G3) k ρ := by
  show (updO (updO (updO (updO T₀ (kv₄ Hb G v) v.v₄.1) (kv₃ Hb G v) v.v₃.1) (kv₂ Hb G v) v.v₂.1)
    (kv₁ Hb G v) v.v₁.1) k ρ = (updO (updO (updO (updO T₀ (kv₄ Hb G v) v.v₄.1) (kv₃ Hb G v)
      G3) (kv₂ Hb G v) v.v₂.1) (kv₁ Hb G v) v.v₁.1) k ρ
  simp only [updO_apply]
  split_ifs <;> simp_all

lemma tabOf_with3₄ (T₀ : H3T) (v : GView S p₁ p₂ p₃ p₄) (G3 : Tab3) (k : Pre) (ρ : Bytes 16)
    (h : kv₄ Hb G v = some k → v.v₄.1 ρ = G3 ρ) :
    tabOf Hb G T₀ v k ρ = tabOf Hb G T₀ (v.with3₄ G3) k ρ := by
  show (updO (updO (updO (updO T₀ (kv₄ Hb G v) v.v₄.1) (kv₃ Hb G v) v.v₃.1) (kv₂ Hb G v) v.v₂.1)
    (kv₁ Hb G v) v.v₁.1) k ρ = (updO (updO (updO (updO T₀ (kv₄ Hb G v) G3) (kv₃ Hb G v)
      v.v₃.1) (kv₂ Hb G v) v.v₂.1) (kv₁ Hb G v) v.v₁.1) k ρ
  simp only [updO_apply]
  split_ifs <;> simp_all

/-- The points of `Q` in the column at an optional prefix. -/
def colPts (Q : Finset (Pre × Bytes 16)) (k : Option Pre) : Finset (Bytes 16) :=
  (Q.filter fun x => k = some x.1).image Prod.snd

lemma card_colPts (Q : Finset (Pre × Bytes 16)) (k : Option Pre) : (colPts Q k).card ≤ Q.card :=
  card_image_le.trans (card_filter_le _ _)

lemma mem_colPts {Q : Finset (Pre × Bytes 16)} {k : Option Pre} {x : Pre × Bytes 16} (hx : x ∈ Q)
    (hk : k = some x.1) : x.2 ∈ colPts Q k :=
  mem_image.2 ⟨x, mem_filter.2 ⟨hx, hk⟩, rfl⟩

/-- **The event of the slice game**: `f` on the table built from the view's slices. It reads the
view as `main_shared23_le` needs: slice `j` at the points of `f`'s `H₃` reads in the column at
proof `j`'s prefix. -/
theorem rdH_tabOf {X : Sort*} {f : GView S p₁ p₂ p₃ p₄ → H3T → X}
    {R5 : GView S p₁ p₂ p₃ p₄ → H3T → Finset (Bytes 37)} {q3 qE : ℕ} (hf : RdH f R5 q3 qE)
    (T₀ : H3T) :
    Rd (fun v => f v (tabOf Hb G T₀ v)) (fun v => R5 v (tabOf Hb G T₀ v)) q3 qE := by
  obtain ⟨QE, hQEc, hQE⟩ := hf.hE
  obtain ⟨QT, hQTc, hQT⟩ := hf.hT
  refine ⟨fun v G5 h => hf.h5 v _ G5 h, ⟨fun v => QE v (tabOf Hb G T₀ v), fun v => hQEc _ _,
    fun v E h => hQE v _ E h⟩, ⟨fun v => colPts (QT v (tabOf Hb G T₀ v)) (kv₁ Hb G v),
    fun v => (card_colPts _ _).trans (hQTc _ _), fun v G3 h => ?_⟩,
    ⟨fun v => colPts (QT v (tabOf Hb G T₀ v)) (kv₂ Hb G v),
    fun v => (card_colPts _ _).trans (hQTc _ _), fun v G3 h => ?_⟩,
    ⟨fun v => colPts (QT v (tabOf Hb G T₀ v)) (kv₃ Hb G v),
    fun v => (card_colPts _ _).trans (hQTc _ _), fun v G3 h => ?_⟩,
    ⟨fun v => colPts (QT v (tabOf Hb G T₀ v)) (kv₄ Hb G v),
    fun v => (card_colPts _ _).trans (hQTc _ _), fun v G3 h => ?_⟩⟩
  · show f (v.with3₁ G3) _ = _
    rw [hf.i₁]
    exact hQT v _ _ fun x hx => tabOf_with3₁ T₀ v G3 x.1 x.2 fun hk => h _ (mem_colPts hx hk)
  · show f (v.with3₂ G3) _ = _
    rw [hf.i₂]
    exact hQT v _ _ fun x hx => tabOf_with3₂ T₀ v G3 x.1 x.2 fun hk => h _ (mem_colPts hx hk)
  · show f (v.with3₃ G3) _ = _
    rw [hf.i₃]
    exact hQT v _ _ fun x hx => tabOf_with3₃ T₀ v G3 x.1 x.2 fun hk => h _ (mem_colPts hx hk)
  · show f (v.with3₄ G3) _ = _
    rw [hf.i₄]
    exact hQT v _ _ fun x hx => tabOf_with3₄ T₀ v G3 x.1 x.2 fun hk => h _ (mem_colPts hx hk)

end Keys

/-! ## The shared game, and the reduction to the slice game -/

section Chain

variable {S : Type} [Fintype S] [Nonempty S] {p₀ : Params} {n₁ n₂ n₃ n₄ : ℕ} (Hb : Hashes)
  (G : Game S Out SW SW SW SW)

/-- **The view of the game with all proofs real and one `H₃`**: slot `j` runs the real prover
with its tape's `ρ`, reading the column of `T` at its prefix. The tape's slices are not read (they
are the view's slice components, which the events ignore). -/
noncomputable def hybVAll (x : GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄)) (T : H3T) :
    GView S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) :=
  viewOf23 G x.1 x.2.2.1.2.2 x.2.1 (realSBT Hb _ x.2.2.1.1.1 x.2.2.1.2.1 T)
    (realSBT Hb _ x.2.2.2.1.1.1 x.2.2.2.1.2.1 T) (realSBT Hb _ x.2.2.2.2.1.1.1 x.2.2.2.2.1.2.1 T)
    (realSBT Hb _ x.2.2.2.2.2.1.1 x.2.2.2.2.2.2.1 T)

/-- **The real game with one `H₃`**: the probability of an event of the view and of `T`. -/
noncomputable def realAll (F : GView S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) → H3T → Prop) :
    ℝ :=
  pr (GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) × H3T) (fun z =>
    F (hybVAll Hb G z.1 z.2) z.2)

/-- **The game with all proofs simulated and one `H₃`** (which no simulator reads). -/
noncomputable def simAll (F : GView S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) → H3T → Prop) :
    ℝ :=
  pr (GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) × H3T) (fun z =>
    F (hybV23 Hb G true true true true z.1) z.2)

lemma withU_u (v : GView S p₁ p₂ p₃ p₄) : v.withU v.u = v := by cases v; rfl

/-- **With different prefixes, the shared game on the table built from the slices is the slice
game.** -/
theorem hybVAll_tabOf (x : GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄)) (T₀ : H3T)
    (hD : DistV Hb G (hybV23 Hb G false false false false x)) :
    hybVAll Hb G x (tabOf Hb G T₀ (hybV23 Hb G false false false false x)) =
      hybV23 Hb G false false false false x := by
  set v := hybV23 Hb G false false false false x with hv
  have h := viewOf23_agree G x.1 x.2.2.1.2.2 x.2.1 x.2.1
    (modeSB Hb _ false x.2.2.1) (realSBT Hb _ x.2.2.1.1.1 x.2.2.1.2.1 (tabOf Hb G T₀ v))
    (modeSB Hb _ false x.2.2.2.1) (realSBT Hb _ x.2.2.2.1.1.1 x.2.2.2.1.2.1 (tabOf Hb G T₀ v))
    (modeSB Hb _ false x.2.2.2.2.1)
    (realSBT Hb _ x.2.2.2.2.1.1.1 x.2.2.2.2.1.2.1 (tabOf Hb G T₀ v))
    (modeSB Hb _ false x.2.2.2.2.2)
    (realSBT Hb _ x.2.2.2.2.2.1.1 x.2.2.2.2.2.2.1 (tabOf Hb G T₀ v))
    (fun sw hsw => by
      have hk : kv₁ Hb G v = some (preOf Hb (pw p₀ n₁) sw) := by
        simp only [kv₁, Option.mem_def] at hsw ⊢; rw [show yv₁ G v = some sw from hsw]; rfl
      show realRO _ Hb _ sw.2 _ (tabOf Hb G T₀ v (preOf Hb (pw p₀ n₁) sw)) _ =
        realRO _ Hb _ sw.2 _ _ _
      rw [tabOf_at₁ hk]; rfl)
    rfl
    (fun sw hsw => by
      have hk : kv₂ Hb G v = some (preOf Hb (pw p₀ n₂) sw) := by
        simp only [kv₂, Option.mem_def] at hsw ⊢; rw [show yv₂ G v = some sw from hsw]; rfl
      show realRO _ Hb _ sw.2 _ (tabOf Hb G T₀ v (preOf Hb (pw p₀ n₂) sw)) _ =
        realRO _ Hb _ sw.2 _ _ _
      rw [tabOf_at₂ hD hk]; rfl)
    rfl
    (fun sw hsw => by
      have hk : kv₃ Hb G v = some (preOf Hb (pw p₀ n₃) sw) := by
        simp only [kv₃, Option.mem_def] at hsw ⊢; rw [show yv₃ G v = some sw from hsw]; rfl
      show realRO _ Hb _ sw.2 _ (tabOf Hb G T₀ v (preOf Hb (pw p₀ n₃) sw)) _ =
        realRO _ Hb _ sw.2 _ _ _
      rw [tabOf_at₃ hD hk]; rfl)
    rfl
    (fun sw hsw => by
      have hk : kv₄ Hb G v = some (preOf Hb (pw p₀ n₄) sw) := by
        simp only [kv₄, Option.mem_def] at hsw ⊢; rw [show yv₄ G v = some sw from hsw]; rfl
      show realRO _ Hb _ sw.2 _ (tabOf Hb G T₀ v (preOf Hb (pw p₀ n₄) sw)) _ =
        realRO _ Hb _ sw.2 _ _ _
      rw [tabOf_at₄ hD hk]; rfl)
    rfl rfl rfl rfl rfl
  exact h.trans (withU_u _)

/-! The prefix of proof `j` does not depend on the slices of proofs `j`, …, `4`. -/

lemma kv₁_s3T₁ (m₁ m₂ m₃ m₄ : Bool) (x : GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄))
    (g : Tab3) :
    kv₁ Hb G (hybV23 Hb G m₁ m₂ m₃ m₄ (s3T₁ x g)) = kv₁ Hb G (hybV23 Hb G m₁ m₂ m₃ m₄ x) := by
  simp only [kv₁, yv₁, hybV23, viewOf23, s3T₁]

lemma kv₁_s3T₂ (m₁ m₂ m₃ m₄ : Bool) (x : GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄))
    (g : Tab3) :
    kv₁ Hb G (hybV23 Hb G m₁ m₂ m₃ m₄ (s3T₂ x g)) = kv₁ Hb G (hybV23 Hb G m₁ m₂ m₃ m₄ x) := by
  simp only [kv₁, yv₁, hybV23, viewOf23, s3T₂]

lemma kv₁_s3T₃ (m₁ m₂ m₃ m₄ : Bool) (x : GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄))
    (g : Tab3) :
    kv₁ Hb G (hybV23 Hb G m₁ m₂ m₃ m₄ (s3T₃ x g)) = kv₁ Hb G (hybV23 Hb G m₁ m₂ m₃ m₄ x) := by
  simp only [kv₁, yv₁, hybV23, viewOf23, s3T₃]

lemma kv₁_s3T₄ (m₁ m₂ m₃ m₄ : Bool) (x : GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄))
    (g : Tab3) :
    kv₁ Hb G (hybV23 Hb G m₁ m₂ m₃ m₄ (s3T₄ x g)) = kv₁ Hb G (hybV23 Hb G m₁ m₂ m₃ m₄ x) := by
  simp only [kv₁, yv₁, hybV23, viewOf23, s3T₄]

lemma kv₂_s3T₂ (m₁ m₂ m₃ m₄ : Bool) (x : GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄))
    (g : Tab3) :
    kv₂ Hb G (hybV23 Hb G m₁ m₂ m₃ m₄ (s3T₂ x g)) = kv₂ Hb G (hybV23 Hb G m₁ m₂ m₃ m₄ x) := by
  simp only [kv₂, yv₂, hybV23, viewOf23, s3T₂]

lemma kv₂_s3T₃ (m₁ m₂ m₃ m₄ : Bool) (x : GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄))
    (g : Tab3) :
    kv₂ Hb G (hybV23 Hb G m₁ m₂ m₃ m₄ (s3T₃ x g)) = kv₂ Hb G (hybV23 Hb G m₁ m₂ m₃ m₄ x) := by
  simp only [kv₂, yv₂, hybV23, viewOf23, s3T₃]

lemma kv₂_s3T₄ (m₁ m₂ m₃ m₄ : Bool) (x : GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄))
    (g : Tab3) :
    kv₂ Hb G (hybV23 Hb G m₁ m₂ m₃ m₄ (s3T₄ x g)) = kv₂ Hb G (hybV23 Hb G m₁ m₂ m₃ m₄ x) := by
  simp only [kv₂, yv₂, hybV23, viewOf23, s3T₄]

lemma kv₃_s3T₃ (m₁ m₂ m₃ m₄ : Bool) (x : GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄))
    (g : Tab3) :
    kv₃ Hb G (hybV23 Hb G m₁ m₂ m₃ m₄ (s3T₃ x g)) = kv₃ Hb G (hybV23 Hb G m₁ m₂ m₃ m₄ x) := by
  simp only [kv₃, yv₃, hybV23, viewOf23, s3T₃]

lemma kv₃_s3T₄ (m₁ m₂ m₃ m₄ : Bool) (x : GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄))
    (g : Tab3) :
    kv₃ Hb G (hybV23 Hb G m₁ m₂ m₃ m₄ (s3T₄ x g)) = kv₃ Hb G (hybV23 Hb G m₁ m₂ m₃ m₄ x) := by
  simp only [kv₃, yv₃, hybV23, viewOf23, s3T₄]

lemma kv₄_s3T₄ (m₁ m₂ m₃ m₄ : Bool) (x : GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄))
    (g : Tab3) :
    kv₄ Hb G (hybV23 Hb G m₁ m₂ m₃ m₄ (s3T₄ x g)) = kv₄ Hb G (hybV23 Hb G m₁ m₂ m₃ m₄ x) := by
  simp only [kv₄, yv₄, hybV23, viewOf23, s3T₄]

variable {Hb G}

/-- **Real side**: the shared game against the slice game with the table built from the slices,
up to two proofs with one prefix. -/
theorem realAll_close {F : GView S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) → H3T → Prop}
    (i₁ : ∀ v T G3, F (v.with3₁ G3) T = F v T) (i₂ : ∀ v T G3, F (v.with3₂ G3) T = F v T)
    (i₃ : ∀ v T G3, F (v.with3₃ G3) T = F v T) (i₄ : ∀ v T G3, F (v.with3₄ G3) T = F v T) :
    |realAll Hb G F - pr (GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) × H3T) (fun z =>
        F (hybV23 Hb G false false false false z.1)
          (tabOf Hb G z.2 (hybV23 Hb G false false false false z.1)))| ≤
      pr (GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄)) (fun x =>
        ¬ DistV Hb G (hybV23 Hb G false false false false x)) := by
  have e := pr_upd4 (fun x => kv₁ Hb G (hybV23 Hb G false false false false x))
    (fun x => kv₂ Hb G (hybV23 Hb G false false false false x))
    (fun x => kv₃ Hb G (hybV23 Hb G false false false false x))
    (fun x => kv₄ Hb G (hybV23 Hb G false false false false x))
    (fun x T => F (hybVAll Hb G x T) T)
    (fun x g T => Iff.of_eq (i₁ (hybVAll Hb G x T) T g))
    (fun x g T => Iff.of_eq (i₂ (hybVAll Hb G x T) T g))
    (fun x g T => Iff.of_eq (i₃ (hybVAll Hb G x T) T g))
    (fun x g T => Iff.of_eq (i₄ (hybVAll Hb G x T) T g))
    (kv₁_s3T₁ Hb G false false false false) (kv₁_s3T₂ Hb G false false false false) (kv₁_s3T₃ Hb G false false false false)
    (kv₁_s3T₄ Hb G false false false false) (kv₂_s3T₂ Hb G false false false false) (kv₂_s3T₃ Hb G false false false false)
    (kv₂_s3T₄ Hb G false false false false) (kv₃_s3T₃ Hb G false false false false) (kv₃_s3T₄ Hb G false false false false)
    (kv₄_s3T₄ Hb G false false false false)
  have hb := pr_prod_fst (β := H3T) (fun x : GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) =>
    ¬ DistV Hb G (hybV23 Hb G false false false false x))
  have ha := abs_pr_sub_le_of_agree
    (fun z : GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) × H3T =>
      F (hybVAll Hb G z.1 (tabOf Hb G z.2 (hybV23 Hb G false false false false z.1)))
        (tabOf Hb G z.2 (hybV23 Hb G false false false false z.1)))
    (fun z => F (hybV23 Hb G false false false false z.1)
      (tabOf Hb G z.2 (hybV23 Hb G false false false false z.1)))
    (fun z => ¬ DistV Hb G (hybV23 Hb G false false false false z.1)) fun z hz => by
      rw [not_not] at hz
      rw [hybVAll_tabOf Hb G z.1 z.2 hz]
  unfold realAll
  rw [← e, ← hb]
  exact ha

/-- **Simulated side**: no simulator reads `H₃`, so the table built from the slices is uniform. -/
theorem simAll_eq {F : GView S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) → H3T → Prop}
    (i₁ : ∀ v T G3, F (v.with3₁ G3) T = F v T) (i₂ : ∀ v T G3, F (v.with3₂ G3) T = F v T)
    (i₃ : ∀ v T G3, F (v.with3₃ G3) T = F v T) (i₄ : ∀ v T G3, F (v.with3₄ G3) T = F v T) :
    pr (GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) × H3T) (fun z =>
        F (hybV23 Hb G true true true true z.1)
          (tabOf Hb G z.2 (hybV23 Hb G true true true true z.1))) = simAll Hb G F :=
  pr_upd4 (fun x => kv₁ Hb G (hybV23 Hb G true true true true x))
    (fun x => kv₂ Hb G (hybV23 Hb G true true true true x))
    (fun x => kv₃ Hb G (hybV23 Hb G true true true true x))
    (fun x => kv₄ Hb G (hybV23 Hb G true true true true x))
    (fun x T => F (hybV23 Hb G true true true true x) T)
    (fun x g T => Iff.of_eq (i₁ (hybV23 Hb G true true true true x) T g))
    (fun x g T => Iff.of_eq (i₂ (hybV23 Hb G true true true true x) T g))
    (fun x g T => Iff.of_eq (i₃ (hybV23 Hb G true true true true x) T g))
    (fun x g T => Iff.of_eq (i₄ (hybV23 Hb G true true true true x) T g))
    (kv₁_s3T₁ Hb G true true true true) (kv₁_s3T₂ Hb G true true true true) (kv₁_s3T₃ Hb G true true true true)
    (kv₁_s3T₄ Hb G true true true true) (kv₂_s3T₂ Hb G true true true true) (kv₂_s3T₃ Hb G true true true true)
    (kv₂_s3T₄ Hb G true true true true) (kv₃_s3T₃ Hb G true true true true) (kv₃_s3T₄ Hb G true true true true)
    (kv₄_s3T₄ Hb G true true true true)

omit [Fintype S] [Nonempty S] in
/-- `bstar` reads its read set at the view only. -/
lemma bstar_congr {p₁ p₂ p₃ p₄ : Params} (Hb : Hashes) (G : Game S Out SW SW SW SW)
    {R R' : GView S p₁ p₂ p₃ p₄ → Finset (Bytes 37)} {v : GView S p₁ p₂ p₃ p₄}
    (h : R v = R' v) : bstar Hb G R v ↔ bstar Hb G R' v := by
  unfold bstar; rw [h]

/-- Averaging a per-fiber bound `ε + c·Pr[B]`. -/
theorem abs_pr_fiber_le_mul {α β : Type*} [Fintype α] [Nonempty α] [Fintype β]
    (P Q B : α × β → Prop) {ε c : ℝ}
    (h : ∀ a, |pr β (fun b => P (a, b)) - pr β (fun b => Q (a, b))| ≤
      ε + c * pr β (fun b => B (a, b))) :
    |pr (α × β) P - pr (α × β) Q| ≤ ε + c * pr (α × β) B := by
  have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [pr_prod, pr_prod, pr_prod, ← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hα,
    div_le_iff₀ hα, add_mul, mul_assoc, div_mul_cancel₀ _ hα.ne']
  calc |∑ a, (pr β (fun b => P (a, b)) - pr β (fun b => Q (a, b)))|
      ≤ ∑ a, |pr β (fun b => P (a, b)) - pr β (fun b => Q (a, b))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : α, (ε + c * pr β (fun b => B (a, b))) := Finset.sum_le_sum fun a _ => h a
    _ = ε * Fintype.card α + c * ∑ a, pr β (fun b => B (a, b)) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm,
          Finset.mul_sum]

variable (Hb G)

/-- **The joint zero-knowledge hop on `main` with one `H₃`, one `H₂³` table, one `H₅` table and
one cipher**, for four proofs in sequence of one QuickSilver degree. See the module docstring. -/
theorem main_sharedAll_le (hm₁ : MainP (pw p₀ n₁)) (hm₂ : MainP (pw p₀ n₂))
    (hm₃ : MainP (pw p₀ n₃)) (hm₄ : MainP (pw p₀ n₄)) (hp₁ : SmallParams (pw p₀ n₁))
    (hp₂ : SmallParams (pw p₀ n₂)) (hp₃ : SmallParams (pw p₀ n₃)) (hp₄ : SmallParams (pw p₀ n₄))
    (hHb : HashesWF Hb) (hv : GValid G (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄))
    (F : GView S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) → H3T → Prop)
    (R5 : GView S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) → H3T → Finset (Bytes 37))
    {q3 qE : ℕ} (hF : RdH F R5 q3 qE) (hR : RdH R5 R5 q3 qE) :
    |realAll Hb G F - simAll Hb G F| ≤
      15 * (εS q3 (qE + 8 * 4607) + Δ23 p₀.qsDegree) +
        15 * simAll Hb G (fun v T => bstar Hb G (fun v => R5 v T) v) +
        pr (GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄)) (fun x =>
          ¬ DistV Hb G (hybV23 Hb G false false false false x)) := by
  have h1 := realAll_close (Hb := Hb) (G := G) hF.i₁ hF.i₂ hF.i₃ hF.i₄
  have hs := simAll_eq (Hb := Hb) (G := G) hF.i₁ hF.i₂ hF.i₃ hF.i₄
  have hb := simAll_eq (Hb := Hb) (G := G) (F := fun v T => bstar Hb G (fun v => R5 v T) v)
    (fun v T G3 => by
      show bstarCore Hb G _ _ _ _ _ _ (R5 (v.with3₁ G3) T) = _
      rw [hR.i₁]; rfl)
    (fun v T G3 => by
      show bstarCore Hb G _ _ _ _ _ _ (R5 (v.with3₂ G3) T) = _
      rw [hR.i₂]; rfl)
    (fun v T G3 => by
      show bstarCore Hb G _ _ _ _ _ _ (R5 (v.with3₃ G3) T) = _
      rw [hR.i₃]; rfl)
    (fun v T G3 => by
      show bstarCore Hb G _ _ _ _ _ _ (R5 (v.with3₄ G3) T) = _
      rw [hR.i₄]; rfl)
  have hT : ∀ T₀ : H3T,
      |pr (GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄)) (fun x =>
          F (hybV23 Hb G false false false false x)
            (tabOf Hb G T₀ (hybV23 Hb G false false false false x))) -
        pr (GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄)) (fun x =>
          F (hybV23 Hb G true true true true x)
            (tabOf Hb G T₀ (hybV23 Hb G true true true true x)))| ≤
      15 * (εS q3 (qE + 8 * 4607) + Δ23 p₀.qsDegree) +
        15 * pr (GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄)) (fun x =>
          bstar Hb G (fun v => R5 v (tabOf Hb G T₀ v)) (hybV23 Hb G true true true true x)) :=
    fun T₀ => main_shared23_le Hb G hm₁ hm₂ hm₃ hm₄ hp₁ hp₂ hp₃ hp₄ hHb hv
      (fun v => F v (tabOf Hb G T₀ v)) (fun v => R5 v (tabOf Hb G T₀ v))
      (rdH_tabOf hF T₀) (rdH_tabOf hR T₀)
  have h2 := abs_pr_fiber_le_mul (α := H3T) (β := GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄))
    (fun z => F (hybV23 Hb G false false false false z.2)
      (tabOf Hb G z.1 (hybV23 Hb G false false false false z.2)))
    (fun z => F (hybV23 Hb G true true true true z.2)
      (tabOf Hb G z.1 (hybV23 Hb G true true true true z.2)))
    (fun z => bstar Hb G (fun v => R5 v (tabOf Hb G z.1 v)) (hybV23 Hb G true true true true z.2))
    (ε := 15 * (εS q3 (qE + 8 * 4607) + Δ23 p₀.qsDegree)) (c := 15) hT
  have c1 : pr (GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) × H3T) (fun z =>
        F (hybV23 Hb G false false false false z.1)
          (tabOf Hb G z.2 (hybV23 Hb G false false false false z.1))) =
      pr (H3T × GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄)) (fun z =>
        F (hybV23 Hb G false false false false z.2)
          (tabOf Hb G z.1 (hybV23 Hb G false false false false z.2))) :=
    pr_equiv (Equiv.prodComm _ _) (fun z : H3T × GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) =>
      F (hybV23 Hb G false false false false z.2)
        (tabOf Hb G z.1 (hybV23 Hb G false false false false z.2)))
  have c2 : pr (GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) × H3T) (fun z =>
        F (hybV23 Hb G true true true true z.1)
          (tabOf Hb G z.2 (hybV23 Hb G true true true true z.1))) =
      pr (H3T × GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄)) (fun z =>
        F (hybV23 Hb G true true true true z.2)
          (tabOf Hb G z.1 (hybV23 Hb G true true true true z.2))) :=
    pr_equiv (Equiv.prodComm _ _) (fun z : H3T × GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) =>
      F (hybV23 Hb G true true true true z.2)
        (tabOf Hb G z.1 (hybV23 Hb G true true true true z.2)))
  have c3 : pr (GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) × H3T) (fun z =>
        bstar Hb G (fun v => R5 v (tabOf Hb G z.2 v)) (hybV23 Hb G true true true true z.1)) =
      pr (H3T × GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄)) (fun z =>
        bstar Hb G (fun v => R5 v (tabOf Hb G z.1 v)) (hybV23 Hb G true true true true z.2)) :=
    pr_equiv (Equiv.prodComm _ _) (fun z : H3T × GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) =>
      bstar Hb G (fun v => R5 v (tabOf Hb G z.1 v)) (hybV23 Hb G true true true true z.2))
  rw [← c1, ← c2, ← c3, hs] at h2
  have hb' : pr (GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) × H3T) (fun z =>
        bstar Hb G (fun v => R5 v (tabOf Hb G z.2 v)) (hybV23 Hb G true true true true z.1)) =
      simAll Hb G (fun v T => bstar Hb G (fun v => R5 v T) v) := by
    rw [← hb]
    exact pr_congr fun z => bstar_congr Hb G rfl
  rw [hb'] at h2
  have := abs_sub_le_iff.1 h1; have := abs_sub_le_iff.1 h2
  rw [abs_sub_le_iff]
  constructor <;> linarith

end Chain


end VoleMole.ZK.Sim
