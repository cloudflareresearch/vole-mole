import VoleMole.Seed.KOS
import VoleMole.Protocols.PomFRIT

/-!
# The VOLE-check value `ũ` determines the witness slope

`lean/docs/security/pomfrit-lemmap-tight.md` §4–§5. Lemma L3 (`KOSGood`) says: on one level set of
the KOS check (one `(ũ, h_V)`), the responses lie on one line. PomFRIT hashes `ũ`, but not `h_V`,
into the target `h`. This file proves that `ũ` alone determines the slope of that line, across all
`h_V`, in two settings:

* **Parallel lines, any response function** (`KOSPar`, `pcross_eq_zero_of_kosPar`,
  `card_not_kosPar_le`). For a set `Pq` of quadruples of challenges fixed before `chall₁`, at most
  `|Pq|·(|F|⁴|T| + (L−1)⁵|F|⁴)` values of `chall₁` allow two pairs of a quadruple of `Pq` to pass the
  check with the same `ũ` (and any two `h_V`) on lines of different slopes.
  `witness_determined`: with `Pq` the quadruples whose two pairs differ on disjoint sets of trees
  (`DisjQuads`, at most `|X|²·∏ᵢ 2|Bᵢ|` of them, `card_disjQuads_le`; `2³⁷⁷` for PomFRIT,
  `pomfrit_par_count`), two accepting sets with the same `ũ`, each with a free tree, have the same
  witness slope `u*`. So the prefix group of the extracted witness is a function of the first
  message and `ũ`.
* **Affine responses, no new event** (`exists_slope_of_kosGood_affine`,
  `witness_determined_affine`). If the response function is affine on `S` (per-tree VOLE rows; the
  CRT masks when the trees agree on the label rows), `KOSGood` alone gives one slope `(u_Q, u_D)`
  for all level sets of `ũ`.

No `sorry`, no `axiom`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace VoleMole.Seed

section Par

variable {X F R M : Type*} [Field F] [AddCommGroup R] [Module F R] [AddCommGroup M] [Module F M]

/-- The parallelism defect of two pairs of responses `(Δ₀, Δ₁)`, `(Δ₂, Δ₃)`: zero iff the two
secants have the same slope (for distinct lifts). `cross e r Δ₀ Δ₁ Δ₂` is the case `Δ₂ = Δ₀`. -/
def pcross (e : X → F) (r : X → R) (q : X × X × X × X) : R :=
  (e q.2.2.2 - e q.2.2.1) • (r q.2.1 - r q.1) - (e q.2.1 - e q.1) • (r q.2.2.2 - r q.2.2.1)

/-- Two pairs passing a linear check with the same `u`, each with its own value: the check hash
kills the parallelism defect. -/
lemma map_pcross_eq_zero (K : R →ₗ[F] M) (e : X → F) (r : X → R) (u h h' : M) {q : X × X × X × X}
    (h₀ : K (r q.1) + e q.1 • u = h) (h₁ : K (r q.2.1) + e q.2.1 • u = h)
    (h₂ : K (r q.2.2.1) + e q.2.2.1 • u = h') (h₃ : K (r q.2.2.2) + e q.2.2.2 • u = h') :
    K (pcross e r q) = 0 := by
  have k₁ : K (r q.2.1 - r q.1) = -((e q.2.1 - e q.1) • u) := by
    rw [map_sub, sub_smul]; linear_combination (norm := module) h₁ - h₀
  have k₂ : K (r q.2.2.2 - r q.2.2.1) = -((e q.2.2.2 - e q.2.2.1) • u) := by
    rw [map_sub, sub_smul]; linear_combination (norm := module) h₃ - h₂
  simp only [pcross, map_sub, map_smul, k₁, k₂, smul_neg, smul_smul, mul_comm]
  abel

/-- Two secants with zero parallelism defect in a row that is affine on each pair have the same
slope. -/
lemma slope_eq_of_pcross {e : X → F} {f : X → F} {q : X × X × X × X} (hd : e q.2.1 ≠ e q.1)
    (hd' : e q.2.2.2 ≠ e q.2.2.1) {v s v' s' : F} (f₀ : f q.1 = v + s * e q.1)
    (f₁ : f q.2.1 = v + s * e q.2.1) (f₂ : f q.2.2.1 = v' + s' * e q.2.2.1)
    (f₃ : f q.2.2.2 = v' + s' * e q.2.2.2)
    (hp : (e q.2.2.2 - e q.2.2.1) * (f q.2.1 - f q.1) -
      (e q.2.1 - e q.1) * (f q.2.2.2 - f q.2.2.1) = 0) : s = s' := by
  have h1 : e q.2.1 - e q.1 ≠ 0 := sub_ne_zero.2 hd
  have h2 : e q.2.2.2 - e q.2.2.1 ≠ 0 := sub_ne_zero.2 hd'
  have key : (e q.2.2.2 - e q.2.2.1) * (e q.2.1 - e q.1) * (s - s') = 0 := by
    rw [f₀, f₁, f₂, f₃] at hp
    linear_combination hp
  rcases mul_eq_zero.1 key with h | h
  · exact absurd h (mul_ne_zero h2 h1)
  · exact sub_eq_zero.1 h

end Par

section KOS

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {X : Type*}

lemma kosValue_eq {T : Finset F} {L : ℕ} (c : Ch F T) (e : X → F) (Q : X → Fin L → F)
    (D : X → Fin 4 → F) (u : Fin 4 → F) (Δ : X) :
    kosValue c e Q D u Δ = kosHashL c (Q Δ, D Δ) + e Δ • u := rfl

/-- `chall₁ = c` is *good for parallelism* on the quadruples `Pq`: no quadruple of `Pq` has a
nonzero parallelism defect in the hashed rows that VOLEHash maps to minus the defect in the direct
masks. -/
def KOSPar {T : Finset F} {L : ℕ} (c : Ch F T) (Pq : Set (X × X × X × X)) (e : X → F)
    (Q : X → Fin L → F) (D : X → Fin 4 → F) : Prop :=
  ∀ q ∈ Pq, pcross e Q q ≠ 0 → voleHash c (pcross e Q q) ≠ -pcross e D q

/-- **`ũ` determines the slope (any response function).** On a `c` good for parallelism, if the
two pairs of a quadruple of `Pq` pass the KOS check with the same `ũ`, each pair with its own
`h_V`, the two secants are parallel, in the hashed rows and in the direct masks. -/
theorem pcross_eq_zero_of_kosPar {T : Finset F} {L : ℕ} {c : Ch F T} {Pq : Set (X × X × X × X)}
    {e : X → F} {Q : X → Fin L → F} {D : X → Fin 4 → F} (hc : KOSPar c Pq e Q D)
    {q : X × X × X × X} (hq : q ∈ Pq) (u h h' : Fin 4 → F)
    (h₀ : kosValue c e Q D u q.1 = h) (h₁ : kosValue c e Q D u q.2.1 = h)
    (h₂ : kosValue c e Q D u q.2.2.1 = h') (h₃ : kosValue c e Q D u q.2.2.2 = h') :
    pcross e Q q = 0 ∧ pcross e D q = 0 := by
  have hK := map_pcross_eq_zero (kosHashL c) e (fun Δ => (Q Δ, D Δ)) u h h' (q := q) h₀ h₁ h₂ h₃
  have hpair : pcross e (fun Δ => (Q Δ, D Δ)) q = (pcross e Q q, pcross e D q) := rfl
  rw [hpair] at hK
  have hK' : voleHash c (pcross e Q q) + pcross e D q = 0 := hK
  have hQ : pcross e Q q = 0 := by
    by_contra hQ
    exact hc q hq hQ (eq_neg_of_add_eq_zero_left hK')
  refine ⟨hQ, ?_⟩
  have h0 : voleHash c (pcross e Q q) = 0 := by
    rw [hQ]; exact (voleHashL c).map_zero
  rwa [h0, zero_add] at hK'

open Classical in
/-- **Parallelism, counting form.** For response functions `(Q, D)` fixed before `chall₁` and a
finite set `Pq` of quadruples, at most `|Pq|·(|F|⁴·|T| + (L−1)⁵·|F|⁴)` of the `|F|⁸·|T|` values of
`chall₁` are not good for parallelism on `Pq`. -/
theorem card_not_kosPar_le (T : Finset F) {L : ℕ} (Pq : Finset (X × X × X × X)) (e : X → F)
    (Q : X → Fin L → F) (D : X → Fin 4 → F) :
    #{c : Ch F T | ¬KOSPar c (Pq : Set (X × X × X × X)) e Q D} ≤
      #Pq * (Fintype.card F ^ 4 * #T + (L - 1) ^ 5 * Fintype.card F ^ 4) := by
  set B := Fintype.card F ^ 4 * #T + (L - 1) ^ 5 * Fintype.card F ^ 4
  let bad : X × X × X × X → Finset (Ch F T) := fun q =>
    {c | pcross e Q q ≠ 0 ∧ voleHash c (pcross e Q q) = -pcross e D q}
  have hsub : ({c : Ch F T | ¬KOSPar c (Pq : Set (X × X × X × X)) e Q D} : Finset _) ⊆
      Pq.biUnion bad := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    by_contra hnot
    refine hc fun q hq hQ hV => hnot ?_
    exact Finset.mem_biUnion.2 ⟨q, Finset.mem_coe.1 hq, by simp [bad, hQ, hV]⟩
  have hbad : ∀ q ∈ Pq, #(bad q) ≤ B := fun q _ => by
    by_cases hQ : pcross e Q q = 0
    · simp [bad, hQ]
    · refine le_trans (Finset.card_le_card fun c hc => ?_)
        (card_voleHashP_eq_le T (hornerPoly_ne_zero hQ) (natDegree_hornerPoly_le _)
          (-pcross e D q))
      simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact hc.2
  calc _ ≤ #(Pq.biUnion bad) := Finset.card_le_card hsub
    _ ≤ ∑ q ∈ Pq, #(bad q) := Finset.card_biUnion_le
    _ ≤ #Pq * B := Finset.sum_le_card_nsmul _ _ _ hbad

open Classical in
/-- Non-vacuity of `KOSPar`: if `|Pq|·(|F|⁴|T| + (L−1)⁵|F|⁴) < |F|⁸|T|`, some `chall₁` is good for
parallelism on `Pq` (and all but that fraction are). -/
theorem exists_kosPar (T : Finset F) {L : ℕ} (Pq : Finset (X × X × X × X)) (e : X → F)
    (Q : X → Fin L → F) (D : X → Fin 4 → F)
    (hlt : #Pq * (Fintype.card F ^ 4 * #T + (L - 1) ^ 5 * Fintype.card F ^ 4) <
      Fintype.card (Ch F T)) :
    ∃ c : Ch F T, KOSPar c (Pq : Set (X × X × X × X)) e Q D := by
  by_contra hno
  push Not at hno
  have hall : ({c : Ch F T | ¬KOSPar c (Pq : Set (X × X × X × X)) e Q D} : Finset _) =
      Finset.univ := Finset.filter_true_of_mem fun c _ => hno c
  have := card_not_kosPar_le T Pq e Q D
  rw [hall, Finset.card_univ] at this
  omega

/-- **`ũ` determines the slope (affine responses), per quadruple.** On a KOS-good `c`, if the
response function translates along `Δ₃ − Δ₂` at `Δ₀` (it does when it is affine on `S`), and the
pairs `(Δ₀, Δ₁)`, `(Δ₂, Δ₃)` each pass the KOS check with the same `ũ` and their own `h_V`, the two
secants are parallel. No event beyond `KOSGood` is used. -/
theorem pcross_eq_zero_of_kosGood_affine [AddCommGroup X] {T : Finset F} {L : ℕ} {c : Ch F T}
    {S : Set X} {e : X →+ F} {Q : X → Fin L → F} {D : X → Fin 4 → F} (hc : KOSGood c S e Q D)
    {q : X × X × X × X} (h0 : q.1 ∈ S) (h1 : q.2.1 ∈ S)
    (htS : q.1 + (q.2.2.2 - q.2.2.1) ∈ S)
    (hQ : Q (q.1 + (q.2.2.2 - q.2.2.1)) = Q q.1 + (Q q.2.2.2 - Q q.2.2.1))
    (hD : D (q.1 + (q.2.2.2 - q.2.2.1)) = D q.1 + (D q.2.2.2 - D q.2.2.1))
    (u : Fin 4 → F) (hA : kosValue c e Q D u q.1 = kosValue c e Q D u q.2.1)
    (hA' : kosValue c e Q D u q.2.2.1 = kosValue c e Q D u q.2.2.2) :
    pcross e Q q = 0 ∧ pcross e D q = 0 := by
  obtain ⟨Δ₀, Δ₁, Δ₂, Δ₃⟩ := q
  dsimp only at h0 h1 htS hQ hD hA hA' ⊢
  set Δt := Δ₀ + (Δ₃ - Δ₂) with hΔt
  -- The translated point passes with `Δ₀`'s value.
  have ht : kosValue c e Q D u Δt = kosValue c e Q D u Δ₀ := by
    have h32 : kosHashL c (Q Δ₃ - Q Δ₂, D Δ₃ - D Δ₂) + (e Δ₃ - e Δ₂) • u = 0 := by
      have := sub_eq_zero.2 hA'.symm
      rw [kosValue_eq, kosValue_eq] at this
      have hsub : kosHashL c (Q Δ₃ - Q Δ₂, D Δ₃ - D Δ₂) =
          kosHashL c (Q Δ₃, D Δ₃) - kosHashL c (Q Δ₂, D Δ₂) := by
        rw [← map_sub]; rfl
      rw [hsub, sub_smul]
      linear_combination (norm := module) this
    have hadd : kosHashL c (Q Δt, D Δt) =
        kosHashL c (Q Δ₀, D Δ₀) + kosHashL c (Q Δ₃ - Q Δ₂, D Δ₃ - D Δ₂) := by
      rw [← map_add, hQ, hD]; rfl
    rw [kosValue_eq, kosValue_eq, hadd, hΔt, map_add, map_sub, add_smul]
    linear_combination (norm := module) h32
  -- `{Δ₀, Δ₁, Δt}` is on one line.
  obtain ⟨uQ, vQ, uD, vD, hline⟩ := hc u (kosValue c e Q D u Δ₀) {Δ₀, Δ₁, Δt}
    (by
      intro Δ hΔ
      rcases hΔ with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact htS)
    (by
      intro Δ hΔ
      rcases hΔ with rfl | rfl | rfl
      · rfl
      · exact hA.symm
      · exact ht)
  have l0 := hline Δ₀ (by simp)
  have l1 := hline Δ₁ (by simp)
  have lt := hline Δt (by simp)
  have het : e Δt = e Δ₀ + (e Δ₃ - e Δ₂) := by rw [hΔt, map_add, map_sub]
  constructor
  · have d1 : Q Δ₁ - Q Δ₀ = (e Δ₁ - e Δ₀) • uQ := by
      rw [l1.1, l0.1, sub_smul]; abel
    have d2 : Q Δ₃ - Q Δ₂ = (e Δ₃ - e Δ₂) • uQ := by
      have : Q Δ₃ - Q Δ₂ = Q Δt - Q Δ₀ := by rw [hQ]; abel
      rw [this, lt.1, l0.1, het, add_smul]; abel
    simp only [pcross, d1, d2, smul_smul, mul_comm, sub_self]
  · have d1 : D Δ₁ - D Δ₀ = (e Δ₁ - e Δ₀) • uD := by
      rw [l1.2, l0.2, sub_smul]; abel
    have d2 : D Δ₃ - D Δ₂ = (e Δ₃ - e Δ₂) • uD := by
      have : D Δ₃ - D Δ₂ = D Δt - D Δ₀ := by rw [hD]; abel
      rw [this, lt.2, l0.2, het, add_smul]; abel
    simp only [pcross, d1, d2, smul_smul, mul_comm, sub_self]

/-- The response function is affine on `S`: `S` is closed under `Δ + (Δ₃ − Δ₂)` and `(Q, D)`
commute with it. -/
def AffineOn [AddCommGroup X] {L : ℕ} (S : Set X) (Q : X → Fin L → F) (D : X → Fin 4 → F) : Prop :=
  ∀ Δ ∈ S, ∀ Δ₂ ∈ S, ∀ Δ₃ ∈ S, Δ + (Δ₃ - Δ₂) ∈ S ∧
    Q (Δ + (Δ₃ - Δ₂)) = Q Δ + (Q Δ₃ - Q Δ₂) ∧ D (Δ + (Δ₃ - Δ₂)) = D Δ + (D Δ₃ - D Δ₂)

/-- Non-vacuity of `AffineOn`: a constant plus an additive map is affine on every additive coset
(here: the whole group). Per-tree VOLE rows `V[j] + Σᵢ u⁽ⁱ⁾[j]·eᵢ(Δᵢ)` have this form. -/
lemma affineOn_univ [AddCommGroup X] {L : ℕ} (vQ : Fin L → F) (fQ : X →+ (Fin L → F))
    (vD : Fin 4 → F) (fD : X →+ (Fin 4 → F)) :
    AffineOn (Set.univ : Set X) (fun Δ => vQ + fQ Δ) (fun Δ => vD + fD Δ) := by
  intro Δ _ Δ₂ _ Δ₃ _
  refine ⟨Set.mem_univ _, ?_, ?_⟩ <;> simp only [map_add, map_sub] <;> abel

/-- **One slope for all level sets (affine responses).** On a KOS-good `c`, for an affine response
function and a `ũ`, there is one slope `(u_Q, u_D)` such that **every** set `A ⊆ S` passing the KOS
check with `ũ` and any `h_V` lies on a line of that slope. So the slope is a function of the first
message, `chall₁` and `ũ`, and can be read off any two points of `S` with the same check value. -/
theorem exists_slope_of_kosGood_affine [AddCommGroup X] {T : Finset F} {L : ℕ} {c : Ch F T}
    {S : Set X} {e : X →+ F} (he : Set.InjOn e S) {Q : X → Fin L → F} {D : X → Fin 4 → F}
    (hc : KOSGood c S e Q D) (haff : AffineOn S Q D) (u : Fin 4 → F) :
    ∃ uQ : Fin L → F, ∃ uD : Fin 4 → F, ∀ (h : Fin 4 → F) (A : Set X), A ⊆ S →
      (∀ Δ ∈ A, kosValue c e Q D u Δ = h) →
      ∃ vQ : Fin L → F, ∃ vD : Fin 4 → F, ∀ Δ ∈ A, Q Δ = vQ + e Δ • uQ ∧ D Δ = vD + e Δ • uD := by
  by_cases hex : ∃ Δ₀ ∈ S, ∃ Δ₁ ∈ S, Δ₀ ≠ Δ₁ ∧ kosValue c e Q D u Δ₀ = kosValue c e Q D u Δ₁
  · obtain ⟨Δ₀, h0, Δ₁, h1, hne, hlev⟩ := hex
    have hd : e Δ₁ - e Δ₀ ≠ 0 := sub_ne_zero.2 fun h => hne (he h0 h1 h.symm)
    refine ⟨(e Δ₁ - e Δ₀)⁻¹ • (Q Δ₁ - Q Δ₀), (e Δ₁ - e Δ₀)⁻¹ • (D Δ₁ - D Δ₀),
      fun h A hA hacc => ?_⟩
    rcases A.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · exact ⟨0, 0, fun _ h => h.elim⟩
    refine ⟨Q a - e a • ((e Δ₁ - e Δ₀)⁻¹ • (Q Δ₁ - Q Δ₀)),
      D a - e a • ((e Δ₁ - e Δ₀)⁻¹ • (D Δ₁ - D Δ₀)), fun Δ hΔ => ?_⟩
    obtain ⟨hS, hQ, hD⟩ := haff Δ₀ h0 a (hA ha) Δ (hA hΔ)
    obtain ⟨pQ, pD⟩ := pcross_eq_zero_of_kosGood_affine hc (q := (Δ₀, Δ₁, a, Δ)) h0 h1 hS hQ hD u
      hlev ((hacc a ha).trans (hacc Δ hΔ).symm)
    simp only [pcross] at pQ pD
    constructor
    · have key : Q Δ - Q a = (e Δ₁ - e Δ₀)⁻¹ • ((e Δ - e a) • (Q Δ₁ - Q Δ₀)) := by
        rw [sub_eq_zero] at pQ
        rw [pQ, smul_smul, inv_mul_cancel₀ hd, one_smul]
      rw [smul_smul, smul_smul] at *
      linear_combination (norm := module) key
    · have key : D Δ - D a = (e Δ₁ - e Δ₀)⁻¹ • ((e Δ - e a) • (D Δ₁ - D Δ₀)) := by
        rw [sub_eq_zero] at pD
        rw [pD, smul_smul, inv_mul_cancel₀ hd, one_smul]
      rw [smul_smul, smul_smul] at *
      linear_combination (norm := module) key
  · push Not at hex
    refine ⟨0, 0, fun h A hA hacc => ?_⟩
    rcases A.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · exact ⟨0, 0, fun _ h => h.elim⟩
    refine ⟨Q a, D a, fun Δ hΔ => ?_⟩
    have : Δ = a := by
      by_contra hne
      exact hex Δ (hA hΔ) a (hA ha) hne ((hacc Δ hΔ).trans (hacc a ha).symm)
    subst this
    simp

/-- On a set with two points, the slope of a consistent row (`Claim4Hyp.consistent`) is the row's
entry of the line's slope. With `exists_slope_of_kosGood_affine`: the witness slope `u*` of every
accepting set is the witness part of the one slope `u_Q` of `ũ`. -/
lemma consistent_slope_eq {L : ℕ} {e : X → F} {A : Set X} {Q : X → Fin L → F} {uQ vQ : Fin L → F}
    (hline : ∀ Δ ∈ A, Q Δ = vQ + e Δ • uQ) {j : Fin L} {v s : F}
    (hcons : ∀ Δ ∈ A, Q Δ j = v + s * e Δ) {Δ₀ Δ₁ : X} (h0 : Δ₀ ∈ A) (h1 : Δ₁ ∈ A)
    (hne : e Δ₁ ≠ e Δ₀) : s = uQ j := by
  have a0 := congrFun (hline Δ₀ h0) j
  have a1 := congrFun (hline Δ₁ h1) j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at a0 a1
  rw [hcons Δ₀ h0] at a0
  rw [hcons Δ₁ h1] at a1
  have key : (e Δ₁ - e Δ₀) * (s - uQ j) = 0 := by linear_combination a1 - a0
  rcases mul_eq_zero.1 key with h | h
  · exact absurd (sub_eq_zero.1 h) hne
  · exact sub_eq_zero.1 h

end KOS

/-! ## Trees: two accepting sets with the same `ũ` hold the same witness -/

section Trees

open VoleMole.SeedExtraction VoleMole.PomFRIT

variable {ι J F : Type*} [Fintype ι] [DecidableEq ι] [Field F]
variable {B : ι → Type*} [∀ i, AddCommGroup (B i)]

/-- The quadruples `(Δ₀, Δ₁, Δ₂, Δ₃)` whose pairs `(Δ₀, Δ₁)` and `(Δ₂, Δ₃)` differ on disjoint
sets of trees. -/
def DisjQuads (B : ι → Type*) :
    Set ((∀ i, B i) × (∀ i, B i) × (∀ i, B i) × (∀ i, B i)) :=
  {q | ∀ i, q.1 i = q.2.1 i ∨ q.2.2.1 i = q.2.2.2 i}

/-- **Two accepting sets, one witness slope (deterministic core).** Let `A` and `A'` be the
accepting sets of two chains over the same committed data (`Claim4Hyp` with the same trees `u` and
rows `Q`), with bit slopes `u*` and `u*'`, each with a free tree. If the secants of `A` and of `A'`
that differ on disjoint sets of trees are parallel in every witness row (`hpar`: what `ũ` gives,
`pcross_eq_zero_of_kosPar`), then `u* = u*'`. -/
theorem uStar_eq_of_parallel {e : (∀ i, B i) →+ F} {A A' : Set (∀ i, B i)} {known : Finset ι}
    {u : ι → J → Bool} {Q : J → (∀ i, B i) → F} {uStar uStar' : J → F}
    (hK : Claim4Hyp e A known u Q uStar) (hK' : Claim4Hyp e A' known u Q uStar')
    (hbits : ∀ j, uStar j = 0 ∨ uStar j = 1) (hbits' : ∀ j, uStar' j = 0 ∨ uStar' j = 1)
    (hpar : ∀ q ∈ DisjQuads B, q.1 ∈ A → q.2.1 ∈ A → q.2.2.1 ∈ A' → q.2.2.2 ∈ A' → ∀ j,
      (e q.2.2.2 - e q.2.2.1) * (Q j q.2.1 - Q j q.1) -
        (e q.2.1 - e q.1) * (Q j q.2.2.2 - Q j q.2.2.1) = 0)
    {i₀ i₁ : ι} (hfree : ¬IsFixed A i₀) (hfree' : ¬IsFixed A' i₁) : uStar = uStar' := by
  by_contra hne
  unfold IsFixed at hfree hfree'
  push Not at hfree hfree'
  obtain ⟨Δ₀, h0, Δ₁, h1, hd⟩ := hfree
  obtain ⟨Δ₂, h2, Δ₃, h3, hd'⟩ := hfree'
  have hq : (Δ₀, Δ₁, Δ₂, Δ₃) ∈ DisjQuads B := by
    intro i
    by_contra hboth
    push Not at hboth
    have f1 : ¬IsFixed A i := fun hf => hboth.1 (hf Δ₀ h0 Δ₁ h1)
    have f2 : ¬IsFixed A' i := fun hf => hboth.2 (hf Δ₂ h2 Δ₃ h3)
    apply hne
    funext j
    rw [← (free_tree_holds_witness hK hbits f1).2 j, ← (free_tree_holds_witness hK' hbits' f2).2 j]
  apply hne
  funext j
  obtain ⟨v, hv⟩ := hK.consistent j
  obtain ⟨v', hv'⟩ := hK'.consistent j
  have e1 : e Δ₁ ≠ e Δ₀ := fun h => hd (congrFun (hK.lift_inj h) i₀).symm
  have e3 : e Δ₃ ≠ e Δ₂ := fun h => hd' (congrFun (hK.lift_inj h) i₁).symm
  exact slope_eq_of_pcross (q := (Δ₀, Δ₁, Δ₂, Δ₃)) (f := Q j) e1 e3 (hv Δ₀ h0) (hv Δ₁ h1)
    (hv' Δ₂ h2) (hv' Δ₃ h3) (hpar _ hq h0 h1 h2 h3 j)

variable [Fintype F] [DecidableEq F]

/-- **`ũ` determines the witness (any response function).** On a `chall₁` good for parallelism on
`DisjQuads`, two accepting sets `A`, `A'` that pass the KOS check with the same `ũ` (and any
`h_V`, `h_V'`), each with a free tree and a bit slope, have the same witness slope: `u* = u*'`.
Hence their free trees hold the same witness rows. -/
theorem witness_determined {T : Finset F} {L ℓ : ℕ} (hℓ : ℓ ≤ L) {c : Ch F T}
    {e : (∀ i, B i) →+ F} {A A' : Set (∀ i, B i)} {known : Finset ι} {u : ι → Fin ℓ → Bool}
    {Q : (∀ i, B i) → Fin L → F} {D : (∀ i, B i) → Fin 4 → F}
    (hc : KOSPar c (DisjQuads B) e Q D) (ũ h h' : Fin 4 → F)
    (hacc : ∀ Δ ∈ A, kosValue c e Q D ũ Δ = h) (hacc' : ∀ Δ ∈ A', kosValue c e Q D ũ Δ = h')
    {uStar uStar' : Fin ℓ → F}
    (hK : Claim4Hyp e A known u (fun j Δ => Q Δ (Fin.castLE hℓ j)) uStar)
    (hK' : Claim4Hyp e A' known u (fun j Δ => Q Δ (Fin.castLE hℓ j)) uStar')
    (hbits : ∀ j, uStar j = 0 ∨ uStar j = 1) (hbits' : ∀ j, uStar' j = 0 ∨ uStar' j = 1)
    {i₀ i₁ : ι} (hfree : ¬IsFixed A i₀) (hfree' : ¬IsFixed A' i₁) :
    uStar = uStar' ∧ ∀ j, u i₀ j = u i₁ j := by
  have hu : uStar = uStar' := by
    refine uStar_eq_of_parallel hK hK' hbits hbits' (fun q hq h0 h1 h2 h3 j => ?_) hfree hfree'
    have hp := (pcross_eq_zero_of_kosPar hc hq ũ h h' (hacc _ h0) (hacc _ h1) (hacc' _ h2)
      (hacc' _ h3)).1
    have := congrFun hp (Fin.castLE hℓ j)
    simpa [pcross] using this
  refine ⟨hu, fun j => ?_⟩
  have a := (free_tree_holds_witness hK hbits hfree).2 j
  have b := (free_tree_holds_witness hK' hbits' hfree').2 j
  rw [hu, ← b] at a
  cases h0 : u i₀ j <;> cases h1 : u i₁ j <;> simp_all [bit]

/-- **`ũ` determines the witness (affine responses, `KOSGood` only).** For an affine response
function on `S`, two accepting sets in `S` that pass the KOS check with the same `ũ`, each with a
free tree and a bit slope, have the same witness slope. -/
theorem witness_determined_affine {T : Finset F} {L ℓ : ℕ} (hℓ : ℓ ≤ L) {c : Ch F T}
    {e : (∀ i, B i) →+ F} {S A A' : Set (∀ i, B i)} {known : Finset ι} {u : ι → Fin ℓ → Bool}
    {Q : (∀ i, B i) → Fin L → F} {D : (∀ i, B i) → Fin 4 → F}
    (hc : KOSGood c S e Q D) (haff : AffineOn S Q D) (hA : A ⊆ S) (hA' : A' ⊆ S)
    (ũ h h' : Fin 4 → F)
    (hacc : ∀ Δ ∈ A, kosValue c e Q D ũ Δ = h) (hacc' : ∀ Δ ∈ A', kosValue c e Q D ũ Δ = h')
    {uStar uStar' : Fin ℓ → F}
    (hK : Claim4Hyp e A known u (fun j Δ => Q Δ (Fin.castLE hℓ j)) uStar)
    (hK' : Claim4Hyp e A' known u (fun j Δ => Q Δ (Fin.castLE hℓ j)) uStar')
    (hbits : ∀ j, uStar j = 0 ∨ uStar j = 1) (hbits' : ∀ j, uStar' j = 0 ∨ uStar' j = 1)
    {i₀ i₁ : ι} (hfree : ¬IsFixed A i₀) (hfree' : ¬IsFixed A' i₁) :
    uStar = uStar' ∧ ∀ j, u i₀ j = u i₁ j := by
  have hu : uStar = uStar' := by
    refine uStar_eq_of_parallel hK hK' hbits hbits' (fun q _ h0 h1 h2 h3 j => ?_) hfree hfree'
    obtain ⟨hS, hQ, hD⟩ := haff q.1 (hA h0) q.2.2.1 (hA' h2) q.2.2.2 (hA' h3)
    have hp := (pcross_eq_zero_of_kosGood_affine hc (q := q) (hA h0) (hA h1) hS hQ hD ũ
      ((hacc _ h0).trans (hacc _ h1).symm) ((hacc' _ h2).trans (hacc' _ h3).symm)).1
    have := congrFun hp (Fin.castLE hℓ j)
    simpa [pcross] using this
  refine ⟨hu, fun j => ?_⟩
  have a := (free_tree_holds_witness hK hbits hfree).2 j
  have b := (free_tree_holds_witness hK' hbits' hfree').2 j
  rw [hu, ← b] at a
  cases h0 : u i₀ j <;> cases h1 : u i₁ j <;> simp_all [bit]

end Trees

/-! ## Counting the quadruples -/

section Count

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {B : ι → Type*} [∀ i, AddCommGroup (B i)] [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]

open Classical in
/-- There are at most `|X|²·∏ᵢ 2|Bᵢ|` quadruples whose pairs differ on disjoint sets of trees
(`X = Πᵢ Bᵢ`): choose `Δ₀`, `Δ₂` and, per tree, the two differences, one of which is zero. -/
theorem card_disjQuads_le :
    #{q : (∀ i, B i) × (∀ i, B i) × (∀ i, B i) × (∀ i, B i) | q ∈ DisjQuads B} ≤
      Fintype.card (∀ i, B i) ^ 2 * ∏ i, (2 * Fintype.card (B i)) := by
  let Z : ∀ i, Finset (B i × B i) := fun i => {p | p.1 = 0 ∨ p.2 = 0}
  have hZ : ∀ i, #(Z i) ≤ 2 * Fintype.card (B i) := fun i => by
    have hsub : Z i ⊆ (({0} : Finset (B i)) ×ˢ Finset.univ) ∪ (Finset.univ ×ˢ ({0} : Finset (B i))) := by
      intro p hp
      simp only [Z, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp only [Finset.mem_union, Finset.mem_product, Finset.mem_singleton, Finset.mem_univ,
        and_true, true_and]
      exact hp
    refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
    simp [two_mul]
  let φ : (∀ i, B i) × (∀ i, B i) × (∀ i, B i) × (∀ i, B i) →
      ((∀ i, B i) × (∀ i, B i)) × (∀ i, B i × B i) :=
    fun q => ((q.1, q.2.2.1), fun i => (q.2.1 i - q.1 i, q.2.2.2 i - q.2.2.1 i))
  have hφ : Function.Injective φ := by
    rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h
    simp only [φ, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, h2⟩ := h
    have hb : b = b' := funext fun i => by
      have := congrArg Prod.fst (congrFun h2 i)
      simpa using this
    have hd : d = d' := funext fun i => by
      have := congrArg Prod.snd (congrFun h2 i)
      simpa using this
    rw [hb, hd]
  calc #{q : (∀ i, B i) × (∀ i, B i) × (∀ i, B i) × (∀ i, B i) | q ∈ DisjQuads B}
      ≤ #((Finset.univ : Finset ((∀ i, B i) × (∀ i, B i))) ×ˢ Fintype.piFinset Z) := by
        refine Finset.card_le_card_of_injOn φ (fun q hq => ?_) hφ.injOn
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hq
        simp only [Finset.coe_product, Finset.coe_univ, Set.mem_prod, Set.mem_univ, true_and,
          Finset.mem_coe, Fintype.mem_piFinset, φ, Z, Finset.mem_filter, Finset.mem_univ]
        intro i
        rcases hq i with h | h
        · exact Or.inl (by rw [h, sub_self])
        · exact Or.inr (by rw [h, sub_self])
    _ = Fintype.card (∀ i, B i) ^ 2 * ∏ i, #(Z i) := by
        rw [Finset.card_product, Fintype.card_piFinset, Finset.card_univ, Fintype.card_prod, sq]
    _ ≤ Fintype.card (∀ i, B i) ^ 2 * ∏ i, (2 * Fintype.card (B i)) :=
        Nat.mul_le_mul_left _ (Finset.prod_le_prod fun i _ => hZ i)

open Classical in
/-- PomFRIT's shapes (one tree of `2⁸` leaves, sixteen of `2⁷`): at most `2³⁷⁷` quadruples. -/
theorem pomfrit_disjQuads_le {B : Fin 17 → Type*} [∀ i, AddCommGroup (B i)] [∀ i, Fintype (B i)]
    [∀ i, DecidableEq (B i)] (hB : ∀ i, Fintype.card (B i) = 2 ^ VoleMole.PomFRIT.width i) :
    #{q : (∀ i, B i) × (∀ i, B i) × (∀ i, B i) × (∀ i, B i) | q ∈ DisjQuads B} ≤ 2 ^ 377 := by
  refine card_disjQuads_le.trans (le_of_eq ?_)
  have h1 : Fintype.card (∀ i, B i) = 2 ^ 120 := by
    rw [Fintype.card_pi]
    simp only [hB, Finset.prod_pow_eq_pow_sum, VoleMole.PomFRIT.width_total]
  have h2 : ∏ i, (2 * Fintype.card (B i)) = 2 ^ 137 := by
    simp only [hB, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.prod_pow_eq_pow_sum, VoleMole.PomFRIT.width_total]
    norm_num
  rw [h1, h2, ← pow_mul, ← pow_add]

/-- **The parallelism event for PomFRIT, as a count.** With `|F| = 2¹²⁸`, `|T| = 2⁶⁴` and
`L = 1441` hashed rows, `2³⁷⁷·(|F|⁴|T| + (L−1)⁵|F|⁴) ≤ 2⁹⁵⁴`: at most a fraction `2⁻¹³⁴` of the
`|F|⁸|T| = 2¹⁰⁸⁸` values of `chall₁`. -/
theorem pomfrit_par_count :
    2 ^ 377 * ((2 ^ 128) ^ 4 * 2 ^ 64 + (1441 - 1) ^ 5 * (2 ^ 128) ^ 4) ≤ 2 ^ 954 := by
  have h : (1441 - 1) ^ 5 ≤ 2 ^ 64 := by norm_num
  calc 2 ^ 377 * ((2 ^ 128) ^ 4 * 2 ^ 64 + (1441 - 1) ^ 5 * (2 ^ 128) ^ 4)
      ≤ 2 ^ 377 * ((2 ^ 128) ^ 4 * 2 ^ 64 + 2 ^ 64 * (2 ^ 128) ^ 4) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _)
    _ = 2 ^ 954 := by
        rw [← pow_mul, mul_comm (2 ^ 64), ← two_mul, ← pow_add, ← pow_succ', ← pow_add]

end Count

end VoleMole.Seed
