import VoleMole.Privacy.SeedXOF
import VoleMole.Privacy.Moussaka
import VoleMole.Privacy.Ratatouille
import VoleMole.Prob.Bytes

/-!
# Hiding of `Com`: what a random-oracle model gives, and why it does not apply to the games

Moussaka's and Ratatouille's privacy theorems (`Privacy.Moussaka.anonymity`,
`Privacy.Ratatouille.unlinkability` and every variant built on them: `*RO_lean_num`, `*RA*`,
`*OC*`, `*Sh*`, `_perm`, `_seed`, `*N_lean_le`, `*P_lean_num`) carry `2·εhide`, where `εhide`
bounds `hidingAdv` of an explicit reduction (`Moussaka.hidingAdv`, `Ratatouille.hidingAdv`). This
file states what a random-oracle bound for that term would be, and shows why it cannot discharge
the hypothesis of the games as they stand.

## What `Com` is

`Com` is **not a SHAKE call**. It is one call of the fixed permutation Keccak-p[800,12],
truncated (`Spec.Moussaka.com`, `Spec.Ratatouille.com`; C++ `src/moussaka/commit.hpp`,
`src/ratatouille/ratatouille.cpp:94-100`):

* Moussaka: `Com(nf, ctx_iss, ctx_red, r) = KP800("mous"‖0‖"c0" ‖ r ‖ 0⁹ ‖ ctx_iss ‖ ctx_red ‖ nf
  ‖ 0¹²)[0..45)`: `|r| = 128`, `|nf| = 192`, output 360 bits;
* Ratatouille: `Com(nf, ctx, t, r) = KP800("rata"‖0‖"c0" ‖ r ‖ 0⁹ ‖ ctx ‖ ⟨t⟩₈ ‖ nf ‖ 0²⁰)[0..32)`:
  `|r| = 128`, `|nf| = 192`, `|t| = 64`, output 256 bits.

The issuance, redemption and spend relations evaluate its round function (the witnesses carry the
states after rounds 5 and 9), so in the games `Com` is concrete code, not a table: the
zero-knowledge hops need the honest witness to satisfy the concrete relation (`IssueRelW`,
`RedeemRelW`, `IssueRel`, `SpendRel`), and a random table in place of `Com` would make every
honest witness invalid. This is `security/moussaka.md` F3 for the privacy games. And the games'
adversaries (and so the reductions) are arbitrary functions: they can evaluate Keccak-p[800] at
will. So no query-counting bound can hold for the concrete hypothesis, and none is claimed:

* **`Moussaka.hidingAdv_bruteForce`**: the distinguisher that searches all `2¹²⁸` openings has
  advantage exactly `1 − p`, `p` the probability that a fresh nullifier `nf*` admits some opening
  of the commitment `t₀` (for a random function, `p ≈ 2⁻¹⁹² + 2⁻²³²`);
* **`Ratatouille.hidingAdv_bruteForce_ge`**: for Ratatouille the same search has advantage
  `≥ 1 − 2⁻¹²⁸`, with no assumption on Keccak (a uniform 256-bit string has an opening with
  probability `≤ 2¹²⁸/2²⁵⁶`).

So `εhide` is a computational assumption on Keccak-p[800,12] for the explicit reductions (as the
games state it), and the generic attack costs `2¹²⁸` Keccak evaluations. `r` is not too short for
the 128-bit level, and it is not reused: each Client draws `(nf, r)` from a fresh seed
(Ratatouille's change tokens a fresh `r'`). It is also the witness prefix `w[0..16)` that
enters the proofs' `H₃` seed input, with the proof's secret 128-bit `ρ`; the games model `H₃` as
per-proof slices, so this does not enter `hidingAdv`.

## The random-oracle statement (a heuristic for the standalone experiment)

The hiding experiment itself contains no proof that evaluates `Com`, so, as Lemma U does for
CT-UF (`security/moussaka.md` §3.2), one may *heuristically* model `Com` as a random function for
it alone. With `Com`'s cells a uniform table `g : K → Y` that the distinguisher reads at `q`
cells (`RdX`, adaptively), keyed injectively by `(nf, r)` (`enc`, with the contexts and the
domain-separation tag fixed: `Com`'s DSTs differ from `Tag`'s in byte 5 and between the protocols
in byte 0, so the cells are disjoint from every other Keccak-p[800] use):

* `abs_pr_com_uniform_le` (generic, `ι` commitments, nullifiers fixed): the real commitments and
  independent uniform values are `Pr[r not injective] + |ι|·q/|R|` apart (`abs_pr_seed_le`).
* **Moussaka's form** (`hidingAdvRO`: two commitments, the committed nullifiers against fresh
  ones): `hidingAdvRO_le`, `≤ 2·(1 + 2q)/|R|`; at `|R| = 2¹²⁸`, `(4q + 2)·2⁻¹²⁸`
  (`hidingAdvRO_num`). The note's generic estimate is `≲ 2(q+1)·2⁻¹²⁸`.
* **Ratatouille's form** (`hidingAdvColRO`: four commitments as columns over the credit value,
  real nullifiers, against independent uniform columns): `hidingAdvColRO_le`,
  `≤ (16 + 4q)/|R|`, `(4q + 16)·2⁻¹²⁸` (`hidingAdvColRO_num`); and for a distinguisher that
  reads each commitment at one fixed credit value (`τ`), against independent uniform values as in
  `Ratatouille.hidingAdv` (`hidingAdvAtRO_le`). Adaptive credit values (the reduction's change
  tokens) are the same lazy-sampling step, on paper. (Reading a cell reads its whole column: a
  query at `(nf, ctx, t, r)` is charged for every `t`, which only overcounts.)

These hold for a random function; Keccak-p[800,12] is a permutation with inverse queries, which
adds the note's `q·2⁻⁴⁴⁰` (Moussaka) and `q·Q_c·2⁻⁵⁴³` (Ratatouille) terms on paper. **They are not
corollaries of the privacy theorems**: they bound the advantage of distinguishers that read a
table, and the reductions of the games read no `Com` table (they compute `Com`). Making `Com` a
table of the games would need relations that do not evaluate it (e.g. a commitment opened outside
the proofs), a protocol change. With SHAKE in place of Keccak-p[800] nothing changes: the
relation would evaluate SHAKE's circuit, and a hash evaluated inside a proof is never a
random-oracle table of the game.
-/

open Finset

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.ComHide

-- `Com` evaluates Keccak-p[800]; nothing below unfolds it.
attribute [local irreducible] VoleMole.Spec.Moussaka.com

/-! ## Collisions of uniform openings -/

section Coll

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S] [Nonempty S]

/-- `|ι|` uniform values collide with probability `≤ |ι|² / |S|` (union bound over ordered
pairs). -/
theorem pr_not_injective_le :
    pr (ι → S) (fun c => ¬ Function.Injective c) ≤ (Fintype.card ι : ℝ) ^ 2 / Fintype.card S := by
  classical
  refine le_trans (pr_mono (Q := fun c => ∃ p : ι × ι, p.1 ≠ p.2 ∧ c p.1 = c p.2) fun c hc => ?_)
    ((pr_exists_le_sum _).trans ?_)
  · by_contra h
    push Not at h
    exact hc fun i j hij => by_contra fun hne => h (i, j) hne hij
  · have hp : ∀ p : ι × ι, pr (ι → S) (fun c => p.1 ≠ p.2 ∧ c p.1 = c p.2) ≤
        1 / Fintype.card S := by
      intro p
      by_cases hp : p.1 = p.2
      · calc pr (ι → S) (fun c => p.1 ≠ p.2 ∧ c p.1 = c p.2)
            ≤ pr (ι → S) (fun _ => False) := pr_mono fun c hc => hc.1 hp
          _ = 0 := by rw [pr_const]; simp
          _ ≤ _ := by positivity
      · exact (pr_mono fun c hc => hc.2).trans (Privacy.pr_coord_eq_le hp)
    calc ∑ p : ι × ι, pr (ι → S) (fun c => p.1 ≠ p.2 ∧ c p.1 = c p.2)
        ≤ ∑ _p : ι × ι, (1 : ℝ) / Fintype.card S := Finset.sum_le_sum fun p _ => hp p
      _ = (Fintype.card ι : ℝ) ^ 2 / Fintype.card S := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul]
        push_cast
        ring

end Coll

/-! ## The generic hop: real commitments against uniform values -/

section Generic

variable {ι N R K Y : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype N] [Nonempty N]
  [Fintype R] [Nonempty R] [Fintype K] [DecidableEq K] [Fintype Y] [Nonempty Y]

/-- An encoding of `(nf, r)` into the table's keys that is injective in the pair. -/
def EncInj (enc : N → R → K) : Prop := ∀ n n' r r', enc n r = enc n' r' → n = n' ∧ r = r'

/-- **One commitment hop, nullifiers fixed.** A run `W g u` that reads the commitment table `g`
at most at `q` cells, given the commitments `u`: with `u` the real commitments
`g (enc (n i) (r i))` at uniform openings `r`, and with `u` uniform and independent of `g`, its
probabilities are `Pr[r not injective] + |ι|·q/|R|` apart. -/
theorem abs_pr_com_uniform_le (enc : N → R → K) (henc : EncInj enc) (n : ι → N)
    (W : (K → Y) → (ι → Y) → Prop) {q : ℕ} (hW : ∀ u, RdX (fun g => W g u) q) :
    |pr ((ι → R) × (K → Y)) (fun z => W z.2 (fun i => z.2 (enc (n i) (z.1 i)))) -
        pr ((K → Y) × (ι → Y)) (fun z => W z.1 z.2)| ≤
      pr (ι → R) (fun r => ¬ Function.Injective r) +
        (Fintype.card ι : ℝ) * q / Fintype.card R := by
  classical
  have h := abs_pr_seed_le (C := ι → R) (T := Unit) (x := fun r i => enc (n i) (r i))
    (fun g u (_ : Unit) => W g u) (q := q) (fun u _ => hW u)
    (δ := (Fintype.card ι : ℝ) * q / Fintype.card R) (fun F hF => by
      refine (pr_exists_le_sum _).trans ?_
      have hi : ∀ i, pr (ι → R) (fun r => enc (n i) (r i) ∈ F) ≤ (q : ℝ) / Fintype.card R := by
        intro i
        let G : Finset R := univ.filter fun r => enc (n i) r ∈ F
        have hG : G.card ≤ q := by
          refine le_trans (Finset.card_le_card_of_injOn (enc (n i)) (fun r hr => by
            simpa [G] using hr) (fun a _ b _ hab => (henc _ _ _ _ hab).2)) hF
        refine le_trans (le_of_eq (pr_congr fun r => ?_)) ((pr_coord_mem_le i G).trans ?_)
        · simp [G]
        · gcongr
      calc ∑ i, pr (ι → R) (fun r => enc (n i) (r i) ∈ F) ≤ ∑ _i : ι, (q : ℝ) / Fintype.card R :=
            Finset.sum_le_sum fun i _ => hi i
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_assoc])
  have hni : pr (ι → R) (fun r => ¬ Function.Injective (fun i => enc (n i) (r i))) ≤
      pr (ι → R) (fun r => ¬ Function.Injective r) :=
    pr_mono fun r hr hinj => hr fun i j hij => hinj (henc _ _ _ _ hij).2
  have e1 : pr ((ι → R) × (Unit × (K → Y)))
        (fun z => W z.2.2 (z.2.2 ∘ fun i => enc (n i) (z.1 i))) =
      pr ((ι → R) × (K → Y)) (fun z => W z.2 (fun i => z.2 (enc (n i) (z.1 i)))) :=
    pr_equiv (Equiv.prodCongr (Equiv.refl _) (Equiv.punitProd _))
      (fun z : (ι → R) × (K → Y) => W z.2 (fun i => z.2 (enc (n i) (z.1 i))))
  have e2 : pr (Unit × ((K → Y) × (ι → Y))) (fun z => W z.2.1 z.2.2) =
      pr ((K → Y) × (ι → Y)) (fun z => W z.1 z.2) :=
    pr_equiv (Equiv.punitProd _) (fun z : (K → Y) × (ι → Y) => W z.1 z.2)
  rw [e1, e2] at h
  linarith

/-- The real commitments with their nullifiers: the tape is the nullifiers, the openings and the
commitment table. -/
def hideRealRO (enc : N → R → K) (D : (K → Y) → (ι → Y) → (ι → N) → Prop)
    (z : (ι → N) × ((ι → R) × (K → Y))) : Prop :=
  D z.2.2 (fun i => z.2.2 (enc (z.1 i) (z.2.1 i))) z.1

/-- Independent uniform commitments with the (real) nullifiers. -/
def hideUnifRO (D : (K → Y) → (ι → Y) → (ι → N) → Prop) (z : (ι → N) × ((K → Y) × (ι → Y))) :
    Prop :=
  D z.2.1 z.2.2 z.1

/-- **The hop with the nullifiers revealed.** -/
theorem abs_pr_hideReal_unif_le (enc : N → R → K) (henc : EncInj enc)
    (D : (K → Y) → (ι → Y) → (ι → N) → Prop) {q : ℕ} (hD : ∀ u n, RdX (fun g => D g u n) q) :
    |pr _ (hideRealRO enc D) - pr _ (hideUnifRO D)| ≤
      pr (ι → R) (fun r => ¬ Function.Injective r) +
        (Fintype.card ι : ℝ) * q / Fintype.card R :=
  abs_pr_prod_sub_le _ _ fun n => abs_pr_com_uniform_le enc henc n (fun g u => D g u n)
    fun u => hD u n

/-! ### Moussaka's form: committed nullifiers against fresh ones -/

/-- The ideal experiment of Moussaka's form: the real commitments, and fresh uniform nullifiers
`z.2.1` revealed in place of the committed ones `z.1`. -/
def hideIdealRO (enc : N → R → K) (D : (K → Y) → (ι → Y) → (ι → N) → Prop)
    (z : (ι → N) × ((ι → N) × ((ι → R) × (K → Y)))) : Prop :=
  D z.2.2.2 (fun i => z.2.2.2 (enc (z.1 i) (z.2.2.1 i))) z.2.1

/-- **The hiding advantage in the random-oracle model** (Moussaka's two-instance form,
`Moussaka.hidingAdv` with `Com` a table). -/
noncomputable def hidingAdvRO (enc : N → R → K) (D : (K → Y) → (ι → Y) → (ι → N) → Prop) : ℝ :=
  |pr _ (hideRealRO enc D) - pr _ (hideIdealRO enc D)|

/-- The ideal experiment against the uniform commitments: the fresh nullifiers are the revealed
ones, the committed ones enter only the commitments. -/
theorem abs_pr_hideIdeal_unif_le (enc : N → R → K) (henc : EncInj enc)
    (D : (K → Y) → (ι → Y) → (ι → N) → Prop) {q : ℕ} (hD : ∀ u n, RdX (fun g => D g u n) q) :
    |pr _ (hideIdealRO enc D) - pr _ (hideUnifRO D)| ≤
      pr (ι → R) (fun r => ¬ Function.Injective r) +
        (Fintype.card ι : ℝ) * q / Fintype.card R := by
  let e : (ι → N) × ((ι → N) × ((ι → R) × (K → Y))) ≃
      (ι → N) × ((ι → N) × ((ι → R) × (K → Y))) :=
    { toFun := fun z => (z.2.1, (z.1, z.2.2))
      invFun := fun z => (z.2.1, (z.1, z.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e (hideIdealRO enc D)]
  refine abs_pr_prod_sub_le _ _ fun n' => ?_
  have hu : pr ((K → Y) × (ι → Y)) (fun b => hideUnifRO D (n', b)) =
      pr ((ι → N) × ((K → Y) × (ι → Y))) (fun z => D z.2.1 z.2.2 n') :=
    (pr_prod_snd (α := ι → N) (fun b : (K → Y) × (ι → Y) => D b.1 b.2 n')).symm
  rw [hu]
  exact abs_pr_prod_sub_le _ _ fun n => abs_pr_com_uniform_le enc henc n
    (fun g u => D g u n') fun u => hD u n'

/-- **Hiding in the random-oracle model, Moussaka's form**: `≤ 2·(Pr[r collide] + |ι|·q/|R|)`
for a distinguisher reading the commitment table at `q` cells. -/
theorem hidingAdvRO_le_gen (enc : N → R → K) (henc : EncInj enc)
    (D : (K → Y) → (ι → Y) → (ι → N) → Prop) {q : ℕ} (hD : ∀ u n, RdX (fun g => D g u n) q) :
    hidingAdvRO enc D ≤ 2 * (pr (ι → R) (fun r => ¬ Function.Injective r) +
      (Fintype.card ι : ℝ) * q / Fintype.card R) := by
  have h1 := abs_pr_hideReal_unif_le enc henc D hD
  have h2 := abs_pr_hideIdeal_unif_le enc henc D hD
  have := abs_sub_le (pr _ (hideRealRO enc D)) (pr _ (hideUnifRO D)) (pr _ (hideIdealRO enc D))
  rw [abs_sub_comm (pr _ (hideUnifRO D))] at this
  unfold hidingAdvRO
  linarith

/-- **Two commitments** (Moussaka): `hidingAdvRO ≤ 2·(1 + 2q)/|R|`. -/
theorem hidingAdvRO_le {N R K Y : Type*} [Fintype N] [Nonempty N] [Fintype R] [Nonempty R]
    [Fintype K] [DecidableEq K] [Fintype Y] [Nonempty Y] (enc : N → R → K) (henc : EncInj enc)
    (D : (K → Y) → (Bool → Y) → (Bool → N) → Prop) {q : ℕ}
    (hD : ∀ u n, RdX (fun g => D g u n) q) :
    hidingAdvRO enc D ≤ 2 * (1 + 2 * q) / Fintype.card R := by
  refine (hidingAdvRO_le_gen enc henc D hD).trans ?_
  have h := pr_bool_not_injective_le (S := R)
  rw [Fintype.card_bool] at *
  have : (2 : ℝ) * (1 + 2 * q) / Fintype.card R =
      2 * (1 / Fintype.card R + (2 : ℕ) * q / Fintype.card R) := by push_cast; ring
  rw [this]
  push_cast at h ⊢
  linarith

/-! ### Ratatouille's form: commitments against uniform values, nullifiers real -/

/-- **The hiding advantage in the random-oracle model, Ratatouille's form**: the commitments are
the table's cells (columns over the credit value), against independent uniform cells; the
nullifiers are revealed in both. -/
noncomputable def hidingAdvColRO (enc : N → R → K) (D : (K → Y) → (ι → Y) → (ι → N) → Prop) : ℝ :=
  |pr _ (hideRealRO enc D) - pr _ (hideUnifRO D)|

/-- `≤ |ι|²/|R| + |ι|·q/|R|`. -/
theorem hidingAdvColRO_le (enc : N → R → K) (henc : EncInj enc)
    (D : (K → Y) → (ι → Y) → (ι → N) → Prop) {q : ℕ} (hD : ∀ u n, RdX (fun g => D g u n) q) :
    hidingAdvColRO enc D ≤
      ((Fintype.card ι : ℝ) ^ 2 + Fintype.card ι * q) / Fintype.card R := by
  refine (abs_pr_hideReal_unif_le enc henc D hD).trans ?_
  have := pr_not_injective_le (ι := ι) (S := R)
  rw [add_div]
  linarith

/-- **Each commitment read at one credit value**: for a distinguisher `E` that sees column `i` only
at the point `τ i`, the uniform columns are independent uniform values, as in
`Ratatouille.hidingAdv`'s ideal experiment. -/
theorem hidingAdvAtRO_le {Cr V : Type*} [Fintype Cr] [DecidableEq Cr] [Fintype V] [Nonempty V]
    (enc : N → R → K) (henc : EncInj enc) (τ : ι → Cr)
    (E : (K → Cr → V) → (ι → V) → (ι → N) → Prop) {q : ℕ}
    (hE : ∀ v n, RdX (fun g => E g v n) q) :
    |pr ((ι → N) × ((ι → R) × (K → Cr → V)))
        (fun z => E z.2.2 (fun i => z.2.2 (enc (z.1 i) (z.2.1 i)) (τ i)) z.1) -
      pr ((ι → N) × ((K → Cr → V) × (ι → V))) (fun z => E z.2.1 z.2.2 z.1)| ≤
      ((Fintype.card ι : ℝ) ^ 2 + Fintype.card ι * q) / Fintype.card R := by
  let D : (K → Cr → V) → (ι → Cr → V) → (ι → N) → Prop := fun g u n => E g (fun i => u i (τ i)) n
  have h := hidingAdvColRO_le enc henc D (q := q) fun u n => hE _ n
  have hu : pr _ (hideUnifRO D) =
      pr ((ι → N) × ((K → Cr → V) × (ι → V))) (fun z => E z.2.1 z.2.2 z.1) := by
    unfold hideUnifRO
    rw [pr_prod, pr_prod]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [pr_prod, pr_prod]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    exact pr_cols τ (fun v => E g v n)
  unfold hidingAdvColRO at h
  rw [hu] at h
  exact h

end Generic

/-! ## At the protocols' sizes: `|r| = 128` bits -/

lemma card_coins16 : Fintype.card (Coins 16) = 2 ^ 128 := by
  rw [Fintype.card_fun, Fintype.card_fin, Prob.card_uint8]; norm_num

/-- **Moussaka's form at `|r| = 128`**: `(4q + 2)·2⁻¹²⁸` (`q` reads of the `Com` table; the
nullifiers of any finite type, 24 bytes in Moussaka). -/
theorem hidingAdvRO_num {N K Y : Type*} [Fintype N] [Nonempty N] [Fintype K] [DecidableEq K]
    [Fintype Y] [Nonempty Y] (enc : N → Coins 16 → K) (henc : EncInj enc)
    (D : (K → Y) → (Bool → Y) → (Bool → N) → Prop) {q : ℕ}
    (hD : ∀ u n, RdX (fun g => D g u n) q) :
    hidingAdvRO enc D ≤ (4 * q + 2) / 2 ^ 128 := by
  have h := hidingAdvRO_le enc henc D hD
  rw [card_coins16] at h
  push_cast at h
  calc _ ≤ _ := h
    _ = _ := by ring

/-- **Ratatouille's form at `|r| = 128`, four commitments**: `(4q + 16)·2⁻¹²⁸`. -/
theorem hidingAdvColRO_num {N K Y : Type*} [Fintype N] [Nonempty N] [Fintype K] [DecidableEq K]
    [Fintype Y] [Nonempty Y] (enc : N → Coins 16 → K) (henc : EncInj enc)
    (D : (K → Y) → (Bool × Bool → Y) → (Bool × Bool → N) → Prop) {q : ℕ}
    (hD : ∀ u n, RdX (fun g => D g u n) q) :
    hidingAdvColRO enc D ≤ (4 * q + 16) / 2 ^ 128 := by
  have h := hidingAdvColRO_le enc henc D hD
  rw [card_coins16, Fintype.card_prod, Fintype.card_bool] at h
  push_cast at h
  calc _ ≤ _ := h
    _ = _ := by ring

/-! ## The concrete hypothesis is computational: brute force over the opening -/

/-- The image of a map from `α` is hit by a uniform `u : β` with probability `≤ |α| / |β|`. -/
lemma pr_exists_eq_le {α β : Type*} [Fintype α] [Fintype β] (f : α → β) :
    pr β (fun u => ∃ a, f a = u) ≤ (Fintype.card α : ℝ) / Fintype.card β := by
  classical
  rw [pr_def]
  gcongr
  calc #{u | ∃ a, f a = u} ≤ (univ.image f).card :=
        card_le_card fun u hu => by simpa using hu
    _ ≤ (univ : Finset α).card := card_image_le
    _ = Fintype.card α := card_univ

section BruteForce

open VoleMole.Spec

/-- Moussaka's brute-force distinguisher: is there an opening of `t₀` for the revealed `nf₀`? -/
def mBrute (ci cr : Spec.Bytes) (z : Spec.Bytes × Spec.Bytes × Spec.Bytes × Spec.Bytes) : Prop :=
  ∃ r : Coins Spec.Moussaka.rBytes, Spec.Moussaka.com z.2.2.1 ci cr (List.ofFn r) = z.1

/-- **Moussaka: brute force wins up to the collision probability.** The search over all `2¹²⁸`
openings has advantage exactly `1 − p`, with `p` the probability that a fresh uniform nullifier
admits an opening of the honest `t₀` (for a random function, `p ≈ 2⁻¹⁹² + 2⁻²³²`). So
`Moussaka.hidingAdv` is not small for unbounded distinguishers, and the games' `εhide` is a
computational assumption. -/
theorem Moussaka.hidingAdv_bruteForce (ci cr : Spec.Bytes) :
    Privacy.Moussaka.hidingAdv ci cr (mBrute ci cr) =
      1 - pr (Privacy.Moussaka.HTape × (Coins Spec.Moussaka.nfBytes × Coins Spec.Moussaka.nfBytes))
        (fun x => ∃ r : Coins Spec.Moussaka.rBytes,
          Spec.Moussaka.com (List.ofFn x.2.1) ci cr (List.ofFn r) =
            Spec.Moussaka.com (List.ofFn x.1.1.1) ci cr (List.ofFn x.1.1.2)) := by
  classical
  have h1 : pr Privacy.Moussaka.HTape (fun x => mBrute ci cr (Privacy.Moussaka.hideReal ci cr x)) =
      1 := by
    rw [pr_congr (Q := fun _ => True) fun x => ⟨fun _ => trivial, fun _ => ⟨x.1.2, rfl⟩⟩,
      pr_const]
    simp
  unfold Privacy.Moussaka.hidingAdv
  rw [h1]
  have h2 := pr_le_one (fun x : Privacy.Moussaka.HTape ×
    (Coins Spec.Moussaka.nfBytes × Coins Spec.Moussaka.nfBytes) =>
      mBrute ci cr (Privacy.Moussaka.hideIdeal ci cr x))
  rw [abs_of_nonneg (by linarith)]
  congr 1

/-- Ratatouille's brute-force distinguisher at a credit value `t₀`: is there an opening of the
first commitment for the revealed first nullifier? -/
def rBrute (ctx : Spec.Ratatouille.Context) (t₀ : Spec.Ratatouille.Credits)
    (n : Privacy.Ratatouille.Quad Spec.Ratatouille.Nullifier)
    (cf : Privacy.Ratatouille.Quad (Spec.Ratatouille.Credits → Spec.Ratatouille.Commitment)) :
    Prop :=
  ∃ r : Coins 16, Spec.Ratatouille.com n.1.1 ctx t₀ (Privacy.Ratatouille.vec r) = cf.1.1 t₀

/-- **Ratatouille: brute force wins with probability `≥ 1 − 2⁻¹²⁸`**, with no assumption on
Keccak: a uniform 32-byte string has an opening (`2¹²⁸` candidates) with probability
`≤ 2¹²⁸/2²⁵⁶`. -/
theorem Ratatouille.hidingAdv_bruteForce_ge (ctx : Spec.Ratatouille.Context)
    (t₀ : Spec.Ratatouille.Credits) :
    1 - 1 / 2 ^ 128 ≤ Privacy.Ratatouille.hidingAdv ctx (rBrute ctx t₀) := by
  classical
  have h1 : pr Privacy.Ratatouille.HTape (fun x => rBrute ctx t₀
      (Privacy.Ratatouille.hideReal ctx x).1 (Privacy.Ratatouille.hideReal ctx x).2) = 1 := by
    rw [pr_congr (Q := fun _ => True) fun x => ⟨fun _ => trivial, fun _ => ⟨x.1.1.2, rfl⟩⟩,
      pr_const]
    simp
  -- the ideal probability: only the first slot `(nf, u)` matters
  have h2 : pr Privacy.Ratatouille.UTape (fun x => rBrute ctx t₀
      (Privacy.Ratatouille.hideIdeal x).1 (Privacy.Ratatouille.hideIdeal x).2) ≤ 1 / 2 ^ 128 := by
    let P : Coins 24 × Coins 32 → Prop := fun a => ∃ r : Coins 16,
      Spec.Ratatouille.com (Privacy.Ratatouille.vec a.1) ctx t₀ (Privacy.Ratatouille.vec r) =
        Privacy.Ratatouille.vec a.2
    have e1 := pr_prod_fst (α := (Coins 24 × Coins 32) × (Coins 24 × Coins 32))
      (β := (Coins 24 × Coins 32) × (Coins 24 × Coins 32)) (fun p => P p.1)
    have e2 := pr_prod_fst (α := Coins 24 × Coins 32) (β := Coins 24 × Coins 32) P
    have hfst : pr Privacy.Ratatouille.UTape (fun x => rBrute ctx t₀
        (Privacy.Ratatouille.hideIdeal x).1 (Privacy.Ratatouille.hideIdeal x).2) =
        pr (Coins 24 × Coins 32) P := by
      rw [← e2, ← e1]
      exact pr_congr fun x => Iff.rfl
    rw [hfst]
    refine Privacy.pr_le_of_forall_fst fun a => ?_
    let f : Coins 16 → Coins 32 := fun r k =>
      (Spec.Ratatouille.com (Privacy.Ratatouille.vec a) ctx t₀ (Privacy.Ratatouille.vec r))[k]
    have hsub : ∀ u : Coins 32, P (a, u) → ∃ r, f r = u := by
      rintro u ⟨r, hr⟩
      refine ⟨r, funext fun k => ?_⟩
      simp only [f, hr, Privacy.Ratatouille.vec]
      exact Vector.getElem_ofFn _
    refine (pr_mono hsub).trans ((pr_exists_eq_le f).trans ?_)
    have h32 : Fintype.card (Coins 32) = 2 ^ 256 := by
      rw [Fintype.card_fun, Fintype.card_fin, Prob.card_uint8]; norm_num
    rw [h32, card_coins16]
    norm_num
  unfold Privacy.Ratatouille.hidingAdv
  rw [h1]
  rw [abs_of_nonneg (by linarith [pr_le_one (fun x : Privacy.Ratatouille.UTape => rBrute ctx t₀
      (Privacy.Ratatouille.hideIdeal x).1 (Privacy.Ratatouille.hideIdeal x).2)])]
  linarith

end BruteForce

end VoleMole.Privacy.ComHide
