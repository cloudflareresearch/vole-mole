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

/-! ## Hidden slices (`pomfrit-lemmap-tight.md` §6)

A *class* `C` is a set of alive trees with the same rows `u_C`. Its *slice* at `g` is the set of
challenges that agree with `g` outside `C`. On a slice the witness rows are affine with slope `u_C`
(`claim4Hyp_slice`), so any two points of one slice with the same check value certify the witness
of every accepted chain with that `ũ` (`slice_collision_sound`). A row whose slope is not a bit
(a label row) confines the accepting set to `|A|² ≤ ∏_{free} |B_i|` (`card_sq_le_of_nonbit_slope`).
-/

section Slice

open VoleMole.SeedExtraction VoleMole.PomFRIT

variable {ι J F : Type*} [Fintype ι] [DecidableEq ι] [Field F]
variable {B : ι → Type*} [∀ i, AddCommGroup (B i)]

/-- The slice of the class `C` at `g`: the challenges that agree with `g` on every tree outside
`C`. -/
def slice (C : Finset ι) (g : ∀ i, B i) : Set (∀ i, B i) := {Δ | ∀ i ∉ C, Δ i = g i}

lemma mem_slice_self (C : Finset ι) (g : ∀ i, B i) : g ∈ slice C g := fun _ _ => rfl

/-- A set on which every tree outside `C` is fixed lies in one slice of `C`. -/
lemma subset_slice_of_fixed {A : Set (∀ i, B i)} {C : Finset ι}
    (hfix : ∀ i ∉ C, IsFixed A i) {g : ∀ i, B i} (hg : g ∈ A) : A ⊆ slice C g :=
  fun Δ hΔ i hi => hfix i hi Δ hΔ g hg

lemma isFixed_of_subset_slice {A : Set (∀ i, B i)} {C : Finset ι} {g : ∀ i, B i}
    (hA : A ⊆ slice C g) {i : ι} (hi : i ∉ C) : IsFixed A i :=
  fun _ hΔ _ hΔ' => (hA hΔ i hi).trans (hA hΔ' i hi).symm

/-- A slice is closed under the translations of `AffineOn`. -/
lemma slice_translate {C : Finset ι} {g Δ Δ₂ Δ₃ : ∀ i, B i} (h : Δ ∈ slice C g)
    (h₂ : Δ₂ ∈ slice C g) (h₃ : Δ₃ ∈ slice C g) : Δ + (Δ₃ - Δ₂) ∈ slice C g := fun i hi => by
  simp [h i hi, h₂ i hi, h₃ i hi]

/-- **The witness rows on a slice.** If the trees of `C` are known and hold the same rows `u_C`,
every subset of a slice of `C` satisfies Claim 4's hypotheses with the bit slope `u_C`: the rows
are `v + u_C·e(Δ)` there. -/
theorem claim4Hyp_slice {e : (∀ i, B i) →+ F} (he : Function.Injective e) {S A : Set (∀ i, B i)}
    {known : Finset ι} {u : ι → J → Bool} {Q : J → (∀ i, B i) → F}
    (htree : ∀ j, ∃ c, ∀ Δ ∈ S, Q j Δ = c + ∑ i ∈ known, bit (u i j) * blockLift e i (Δ i))
    {C : Finset ι} (hC : C ⊆ known) {uC : J → Bool} (huC : ∀ i ∈ C, ∀ j, u i j = uC j)
    {g : ∀ i, B i} (hAS : A ⊆ S) (hA : A ⊆ slice C g) :
    Claim4Hyp e A known u Q (fun j => bit (uC j)) where
  lift_inj := he
  tree_form j := by
    obtain ⟨c, hc⟩ := htree j
    exact ⟨c, fun Δ hΔ => hc Δ (hAS hΔ)⟩
  consistent j := by
    obtain ⟨c, hc⟩ := htree j
    refine ⟨c + ∑ i ∈ known \ C, bit (u i j) * blockLift e i (g i) -
      bit (uC j) * ∑ i ∈ Finset.univ \ C, blockLift e i (g i), fun Δ hΔ => ?_⟩
    have h1 : ∑ i ∈ known, bit (u i j) * blockLift e i (Δ i) =
        ∑ i ∈ known \ C, bit (u i j) * blockLift e i (g i) +
          bit (uC j) * ∑ i ∈ C, blockLift e i (Δ i) := by
      rw [← Finset.sum_sdiff hC, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun i hi => by rw [hA hΔ i (Finset.mem_sdiff.1 hi).2]
      · exact Finset.sum_congr rfl fun i hi => by rw [huC i hi j]
    have h2 : e Δ = ∑ i ∈ Finset.univ \ C, blockLift e i (g i) + ∑ i ∈ C, blockLift e i (Δ i) := by
      rw [lift_eq_sum e Δ, ← Finset.sum_sdiff (Finset.subset_univ C)]
      congr 1
      exact Finset.sum_congr rfl fun i hi => by rw [hA hΔ i (Finset.mem_sdiff.1 hi).2]
    rw [hc Δ (hAS hΔ), h1, h2]
    ring
  unknown_fixed i hi := isFixed_of_subset_slice hA fun hiC => hi (hC hiC)

/-- **A row with a slope that is not a bit confines the accepting set.** Under Claim 4's
hypotheses with any slopes, if the slope of row `j` on `A` is neither `0` nor `1` and every tree
outside `G` is fixed on `A`, then `|A|² ≤ ∏_{i ∈ G} |B_i|`: the blocks of the trees of `G` with
`u^{(i)}[j] = 1` determine the challenge, and so do the blocks of the others. (For PomFRIT's label
rows and `G` a group of width at most 57: `|A| ≤ 2²⁸`.) -/
theorem card_sq_le_of_nonbit_slope [∀ i, Fintype (B i)] {e : (∀ i, B i) →+ F}
    {A : Finset (∀ i, B i)} {known : Finset ι} {u : ι → J → Bool} {Q : J → (∀ i, B i) → F}
    {uStar : J → F} (h : Claim4Hyp e (A : Set (∀ i, B i)) known u Q uStar) {j : J}
    (h0 : uStar j ≠ 0) (h1 : uStar j ≠ 1) (G : Finset ι)
    (hfix : ∀ i ∉ G, IsFixed (A : Set (∀ i, B i)) i) :
    A.card ^ 2 ≤ ∏ i ∈ G, Fintype.card (B i) := by
  classical
  obtain ⟨c, hc⟩ := h.tree_form j
  obtain ⟨v, hv⟩ := h.consistent j
  set P : Finset ι := G.filter fun i => i ∈ known ∧ u i j = true with hP
  -- The two forms of `Q[j](Δ) - Q[j](Δ')`.
  have key : ∀ Δ ∈ A, ∀ Δ' ∈ A,
      (∑ i ∈ known, bit (u i j) * blockLift e i (Δ i - Δ' i) =
        uStar j * ∑ i, blockLift e i (Δ i - Δ' i)) ∧
      e Δ - e Δ' = ∑ i, blockLift e i (Δ i - Δ' i) := by
    intro Δ hΔ Δ' hΔ'
    have hall : e Δ - e Δ' = ∑ i, blockLift e i (Δ i - Δ' i) := by
      rw [lift_eq_sum e Δ, lift_eq_sum e Δ', ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => (map_sub _ _ _).symm
    refine ⟨?_, hall⟩
    have e1 := (hc Δ hΔ).symm.trans (hv Δ hΔ)
    have e2 := (hc Δ' hΔ').symm.trans (hv Δ' hΔ')
    rw [← hall]
    simp only [map_sub, mul_sub, Finset.sum_sub_distrib]
    linear_combination e1 - e2
  have hzero : ∀ Δ ∈ A, ∀ Δ' ∈ A, ∀ i, i ∉ G ∨ i ∉ known → blockLift e i (Δ i - Δ' i) = 0 := by
    intro Δ hΔ Δ' hΔ' i hi
    have : Δ i = Δ' i := by
      rcases hi with hi | hi
      · exact hfix i hi Δ hΔ Δ' hΔ'
      · exact h.unknown_fixed i hi Δ hΔ Δ' hΔ'
    rw [this, sub_self, map_zero]
  have hfin : ∀ Δ ∈ A, ∀ Δ' ∈ A, ∑ i, blockLift e i (Δ i - Δ' i) = 0 → Δ = Δ' := by
    intro Δ hΔ Δ' hΔ' hs
    exact h.lift_inj (sub_eq_zero.1 (((key Δ hΔ Δ' hΔ').2).trans hs))
  -- The blocks of `P` determine the challenge.
  have inj1 : ∀ Δ ∈ A, ∀ Δ' ∈ A, (∀ i ∈ P, Δ i = Δ' i) → Δ = Δ' := by
    intro Δ hΔ Δ' hΔ' hag
    refine hfin Δ hΔ Δ' hΔ' ?_
    have hl : ∑ i ∈ known, bit (u i j) * blockLift e i (Δ i - Δ' i) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      by_cases hiG : i ∈ G
      · cases hu : u i j
        · simp [bit]
        · have : i ∈ P := by simp [hP, hiG, hi, hu]
          rw [hag i this, sub_self, map_zero, mul_zero]
      · rw [hzero Δ hΔ Δ' hΔ' i (Or.inl hiG), mul_zero]
    have := (key Δ hΔ Δ' hΔ').1
    rw [hl] at this
    exact (mul_eq_zero.1 this.symm).resolve_left h0
  -- The blocks of `G \ P` determine the challenge.
  have inj2 : ∀ Δ ∈ A, ∀ Δ' ∈ A, (∀ i ∈ G \ P, Δ i = Δ' i) → Δ = Δ' := by
    intro Δ hΔ Δ' hΔ' hag
    refine hfin Δ hΔ Δ' hΔ' ?_
    have hl : ∑ i ∈ known, bit (u i j) * blockLift e i (Δ i - Δ' i) =
        ∑ i, blockLift e i (Δ i - Δ' i) := by
      rw [← Finset.sum_subset (Finset.subset_univ known) fun i _ hi =>
        hzero Δ hΔ Δ' hΔ' i (Or.inr hi)]
      refine Finset.sum_congr rfl fun i hi => ?_
      by_cases hiP : i ∈ P
      · have : u i j = true := (Finset.mem_filter.1 hiP).2.2
        simp [bit, this]
      · by_cases hiG : i ∈ G
        · rw [hag i (Finset.mem_sdiff.2 ⟨hiG, hiP⟩), sub_self, map_zero, mul_zero]
        · rw [hzero Δ hΔ Δ' hΔ' i (Or.inl hiG), mul_zero]
    have := (key Δ hΔ Δ' hΔ').1
    rw [hl] at this
    have h1' : (1 - uStar j) * ∑ i, blockLift e i (Δ i - Δ' i) = 0 := by
      linear_combination this
    exact (mul_eq_zero.1 h1').resolve_left (sub_ne_zero.2 (Ne.symm h1))
  have card_le : ∀ P' : Finset ι, (∀ Δ ∈ A, ∀ Δ' ∈ A, (∀ i ∈ P', Δ i = Δ' i) → Δ = Δ') →
      A.card ≤ ∏ i ∈ P', Fintype.card (B i) := by
    intro P' hinj
    let f : (∀ i, B i) → (∀ i : P', B i) := fun Δ i => Δ i
    have hf : Set.InjOn f (A : Set (∀ i, B i)) := fun Δ hΔ Δ' hΔ' heq =>
      hinj Δ hΔ Δ' hΔ' fun i hi => congrFun heq ⟨i, hi⟩
    calc A.card ≤ (Finset.univ : Finset (∀ i : P', B i)).card :=
          Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) hf
      _ = ∏ i : P', Fintype.card (B i) := by rw [Finset.card_univ, Fintype.card_pi]
      _ = ∏ i ∈ P', Fintype.card (B i) := Finset.prod_coe_sort P' (fun i => Fintype.card (B i))
  calc A.card ^ 2 = A.card * A.card := sq _
    _ ≤ (∏ i ∈ G \ P, Fintype.card (B i)) * ∏ i ∈ P, Fintype.card (B i) :=
        Nat.mul_le_mul (card_le _ inj2) (card_le _ inj1)
    _ = ∏ i ∈ G, Fintype.card (B i) := Finset.prod_sdiff (Finset.filter_subset _ _)

variable [Fintype F] [DecidableEq F]

/-- **A collision in a slice is a certificate.** Let `chall₁` be good for parallelism on
`DisjQuads`, and let `A` be the accepting set of a chain with a bit slope `u*` and a free tree.
If two distinct challenges of one slice of a class `C` (known trees with the same witness rows
`u_C`) have the same check value for the chain's `ũ`, then `u* = u_C`: the chain's witness is the
one the trees of `C` hold. So an extractor that finds such a pair may output the prefix of `C`. -/
theorem slice_collision_sound {T : Finset F} {L ℓ : ℕ} (hℓ : ℓ ≤ L) {c : Ch F T}
    {e : (∀ i, B i) →+ F} {S A : Set (∀ i, B i)} {known : Finset ι} {u : ι → Fin ℓ → Bool}
    {Q : (∀ i, B i) → Fin L → F} {D : (∀ i, B i) → Fin 4 → F}
    (hc : KOSPar c (DisjQuads B) e Q D) (ũ h : Fin 4 → F)
    (hacc : ∀ Δ ∈ A, kosValue c e Q D ũ Δ = h) {uStar : Fin ℓ → F}
    (hK : Claim4Hyp e A known u (fun j Δ => Q Δ (Fin.castLE hℓ j)) uStar)
    (hbits : ∀ j, uStar j = 0 ∨ uStar j = 1) {i₀ : ι} (hfree : ¬IsFixed A i₀)
    (htree : ∀ j, ∃ c', ∀ Δ ∈ S,
      Q Δ (Fin.castLE hℓ j) = c' + ∑ i ∈ known, bit (u i j) * blockLift e i (Δ i))
    {C : Finset ι} (hC : C ⊆ known) {uC : Fin ℓ → Bool} (huC : ∀ i ∈ C, ∀ j, u i j = uC j)
    {g Δ₀ Δ₁ : ∀ i, B i} (h0S : Δ₀ ∈ S) (h1S : Δ₁ ∈ S) (h0 : Δ₀ ∈ slice C g)
    (h1 : Δ₁ ∈ slice C g) (hne : Δ₀ ≠ Δ₁)
    (hcol : kosValue c e Q D ũ Δ₀ = kosValue c e Q D ũ Δ₁) :
    uStar = fun j => bit (uC j) := by
  have hsub : ({Δ₀, Δ₁} : Set (∀ i, B i)) ⊆ S := by
    rintro Δ (rfl | rfl)
    · exact h0S
    · exact h1S
  have hsl : ({Δ₀, Δ₁} : Set (∀ i, B i)) ⊆ slice C g := by
    rintro Δ (rfl | rfl)
    · exact h0
    · exact h1
  have hK' := claim4Hyp_slice (Q := fun j Δ => Q Δ (Fin.castLE hℓ j)) hK.lift_inj htree hC huC
    hsub hsl
  obtain ⟨i₁, hi₁⟩ := Function.ne_iff.1 hne
  have hfree' : ¬IsFixed ({Δ₀, Δ₁} : Set (∀ i, B i)) i₁ := fun hf =>
    hi₁ (hf Δ₀ (by simp) Δ₁ (by simp))
  refine (witness_determined hℓ hc ũ h (kosValue c e Q D ũ Δ₀) hacc ?_ hK hK' hbits
    (fun j => ?_) hfree hfree').1
  · rintro Δ (rfl | rfl)
    · rfl
    · exact hcol.symm
  · cases uC j <;> simp [bit]

/-- `KOSGood` passes to subsets of `S`. -/
lemma KOSGood.mono {X : Type*} {T : Finset F} {L : ℕ} {c : Ch F T} {S S' : Set X} {e : X → F}
    {Q : X → Fin L → F} {D : X → Fin 4 → F} (hc : KOSGood c S e Q D) (h : S' ⊆ S) :
    KOSGood c S' e Q D := fun u h' A hA => hc u h' A (hA.trans h)

/-- **On the right slice, `E₁^lin` needs no new event.** Let `chall₁` be KOS-good and let the
response function be affine on a slice of the class `C` (it is when the trees of `C` agree on the
label rows, `translateOn_gate_slice`). If the accepting set `A` of a chain lies in that slice, any
two distinct challenges of the slice with the same check value give `u* = u_C`. -/
theorem slice_collision_sound_affine {T : Finset F} {L ℓ : ℕ} (hℓ : ℓ ≤ L) {c : Ch F T}
    {e : (∀ i, B i) →+ F} {S A : Set (∀ i, B i)} {known : Finset ι} {u : ι → Fin ℓ → Bool}
    {Q : (∀ i, B i) → Fin L → F} {D : (∀ i, B i) → Fin 4 → F} {C : Finset ι} {g : ∀ i, B i}
    (hc : KOSGood c S e Q D) (haff : AffineOn (S ∩ slice C g) Q D) (hA : A ⊆ S ∩ slice C g)
    (ũ h : Fin 4 → F) (hacc : ∀ Δ ∈ A, kosValue c e Q D ũ Δ = h) {uStar : Fin ℓ → F}
    (hK : Claim4Hyp e A known u (fun j Δ => Q Δ (Fin.castLE hℓ j)) uStar)
    (hbits : ∀ j, uStar j = 0 ∨ uStar j = 1) {i₀ : ι} (hfree : ¬IsFixed A i₀)
    (htree : ∀ j, ∃ c', ∀ Δ ∈ S,
      Q Δ (Fin.castLE hℓ j) = c' + ∑ i ∈ known, bit (u i j) * blockLift e i (Δ i))
    (hC : C ⊆ known) {uC : Fin ℓ → Bool} (huC : ∀ i ∈ C, ∀ j, u i j = uC j)
    {Δ₀ Δ₁ : ∀ i, B i} (h0 : Δ₀ ∈ S ∩ slice C g) (h1 : Δ₁ ∈ S ∩ slice C g) (hne : Δ₀ ≠ Δ₁)
    (hcol : kosValue c e Q D ũ Δ₀ = kosValue c e Q D ũ Δ₁) :
    uStar = fun j => bit (uC j) := by
  have hsub : ({Δ₀, Δ₁} : Set (∀ i, B i)) ⊆ S ∩ slice C g := by
    rintro Δ (rfl | rfl)
    · exact h0
    · exact h1
  have hK' := claim4Hyp_slice (Q := fun j Δ => Q Δ (Fin.castLE hℓ j)) hK.lift_inj htree hC huC
    (hsub.trans Set.inter_subset_left) (hsub.trans Set.inter_subset_right)
  obtain ⟨i₁, hi₁⟩ := Function.ne_iff.1 hne
  have hfree' : ¬IsFixed ({Δ₀, Δ₁} : Set (∀ i, B i)) i₁ := fun hf =>
    hi₁ (hf Δ₀ (by simp) Δ₁ (by simp))
  refine (witness_determined_affine hℓ (hc.mono Set.inter_subset_left) haff hA hsub ũ h
    (kosValue c e Q D ũ Δ₀) hacc ?_ hK hK' hbits (fun j => ?_) hfree hfree').1
  · rintro Δ (rfl | rfl)
    · rfl
    · exact hcol.symm
  · cases uC j <;> simp [bit]

end Slice

/-! ## Gates with two labels are affine (`pomfrit-lemmap-tight.md` §6.2)

The gate term of a CRT mask is `T(L(Δ)) + γ(Δ)·c` with `T` a hash, `L` the gate's label and `γ` its
selection bit. On a slice of a class whose trees agree on the label rows, the label takes two
values, selected by a bit `β(Δ)` that is additive in `Δ`, and `γ = b₀ + β`. Such a term commutes
with the translations of `AffineOn`, whatever `T` is, in characteristic 2. -/

section Gate

variable {X R : Type*} [AddCommGroup X] [AddCommGroup R]

/-- `f` commutes with the translations of `AffineOn` on `S`. -/
def TranslateOn (S : Set X) (f : X → R) : Prop :=
  ∀ Δ ∈ S, ∀ Δ₂ ∈ S, ∀ Δ₃ ∈ S, f (Δ + (Δ₃ - Δ₂)) = f Δ + (f Δ₃ - f Δ₂)

lemma TranslateOn.add {S : Set X} {f f' : X → R} (hf : TranslateOn S f) (hf' : TranslateOn S f') :
    TranslateOn S fun Δ => f Δ + f' Δ := fun Δ hΔ Δ₂ h₂ Δ₃ h₃ => by
  show f _ + f' _ = f Δ + f' Δ + (f Δ₃ + f' Δ₃ - (f Δ₂ + f' Δ₂))
  rw [hf Δ hΔ Δ₂ h₂ Δ₃ h₃, hf' Δ hΔ Δ₂ h₂ Δ₃ h₃]; abel

lemma TranslateOn.sum {κ : Type*} {S : Set X} (s : Finset κ) {f : κ → X → R}
    (hf : ∀ k ∈ s, TranslateOn S (f k)) : TranslateOn S fun Δ => ∑ k ∈ s, f k Δ :=
  fun Δ hΔ Δ₂ h₂ Δ₃ h₃ => by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k hk => hf k hk Δ hΔ Δ₂ h₂ Δ₃ h₃

lemma TranslateOn.comp {R' : Type*} [AddCommGroup R'] {S : Set X} {f : X → R}
    (hf : TranslateOn S f) (φ : R →+ R') : TranslateOn S fun Δ => φ (f Δ) :=
  fun Δ hΔ Δ₂ h₂ Δ₃ h₃ => by
    show φ (f _) = φ (f Δ) + (φ (f Δ₃) - φ (f Δ₂))
    rw [hf Δ hΔ Δ₂ h₂ Δ₃ h₃, map_add, map_sub]

/-- **A function of one additive bit is affine in characteristic 2.** -/
theorem translateOn_bit (S : Set X) (hR : ∀ r : R, r + r = 0) (β : X →+ ZMod 2)
    (ψ : ZMod 2 → R) : TranslateOn S fun Δ => ψ (β Δ) := by
  intro Δ _ Δ₂ _ Δ₃ _
  have hneg : ∀ r : R, -r = r := fun r => neg_eq_of_add_eq_zero_left (hR r)
  have h3 : ∀ a b : R, a + (b + a) = b := fun a b => by rw [add_left_comm, hR, add_zero]
  have h3' : ∀ a b : R, a + (a + b) = b := fun a b => by rw [← add_assoc, hR, zero_add]
  have h01 : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
  have e1 : (1 : ZMod 2) + 1 = 0 := by decide
  have e2 : (-1 : ZMod 2) = 1 := by decide
  have key : ∀ b b₂ b₃ : ZMod 2, ψ (b + (b₃ - b₂)) = ψ b + (ψ b₃ - ψ b₂) := by
    intro b b₂ b₃
    rw [sub_eq_add_neg (ψ b₃), hneg]
    rcases h01 b with rfl | rfl <;> rcases h01 b₂ with rfl | rfl <;>
      rcases h01 b₃ with rfl | rfl <;> simp [hR, h3, h3', e1, e2]
  simpa only [map_add, map_sub] using key (β Δ) (β Δ₂) (β Δ₃)

/-- **Gates with two labels.** If on `S` the gate's label is `L₀` or `L₀ + ℓ` according to an
additive bit `β`, and its selection bit is `b₀ + β`, the gate term `T(L) + γ·c` commutes with
translations on `S`, for every hash `T`. -/
theorem translateOn_gate {Lab : Type*} [AddCommGroup Lab] (S : Set X) (hR : ∀ r : R, r + r = 0)
    (β : X →+ ZMod 2) (T : Lab → R) (cm : R) (L₀ ℓ : Lab) (b₀ : ZMod 2) {lab : X → Lab}
    {γ : X → ZMod 2} (hlab : ∀ Δ ∈ S, lab Δ = if β Δ = 1 then L₀ + ℓ else L₀)
    (hγ : ∀ Δ ∈ S, γ Δ = b₀ + β Δ) (hS : ∀ Δ ∈ S, ∀ Δ₂ ∈ S, ∀ Δ₃ ∈ S, Δ + (Δ₃ - Δ₂) ∈ S) :
    TranslateOn S fun Δ => T (lab Δ) + if γ Δ = 1 then cm else 0 := by
  have h := translateOn_bit S hR β fun b =>
    T (if b = 1 then L₀ + ℓ else L₀) + if b₀ + b = 1 then cm else 0
  intro Δ hΔ Δ₂ h₂ Δ₃ h₃
  have ht := hS Δ hΔ Δ₂ h₂ Δ₃ h₃
  have := h Δ hΔ Δ₂ h₂ Δ₃ h₃
  simp only at this
  dsimp only
  rw [hlab _ ht, hγ _ ht, hlab Δ hΔ, hγ Δ hΔ, hlab Δ₂ h₂, hγ Δ₂ h₂, hlab Δ₃ h₃, hγ Δ₃ h₃]
  exact this

/-- With labels of exponent 2, a sum of copies of `ℓ` selected by bits is `ℓ` selected by the sum
of the bits. -/
lemma sum_ite_bit {κ Lab : Type*} [AddCommGroup Lab] (hLab : ∀ l : Lab, l + l = 0) (ℓ : Lab)
    (s : Finset κ) (b : κ → ZMod 2) :
    (∑ i ∈ s, if b i = 1 then ℓ else 0) = if ∑ i ∈ s, b i = 1 then ℓ else 0 := by
  classical
  have h01 : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ih]
    rcases h01 (b a) with h | h <;> rcases h01 (∑ i ∈ s, b i) with h' | h' <;>
      simp [h, h', hLab, show (1 : ZMod 2) + 1 = 0 from by decide]

/-- **The gate terms are affine on a slice.** Model of one gate of a CRT mask: tree `i`
contributes the bit `γ_i(Δ_i)` to the gate's selection bit and, if that bit is set, its label
offset `ℓ_i` to the gate's label `C₀ + Σ_i γ_i(Δ_i)·ℓ_i`; the gate term is
`T(label) + (selection bit)·c`. If the trees of `C` have the same label offset, the gate term
commutes with translations on every slice of `C`, for every hash `T` and every `c_mult` value. -/
theorem translateOn_gate_slice {ι Lab : Type*} [Fintype ι] [DecidableEq ι] {B : ι → Type*}
    [∀ i, AddCommGroup (B i)] [AddCommGroup Lab] (hR : ∀ r : R, r + r = 0)
    (hLab : ∀ l : Lab, l + l = 0) (γ : ∀ i, B i →+ ZMod 2) (ℓs : ι → Lab) (C₀ : Lab) (T : Lab → R)
    (cm : R) (C : Finset ι) {ℓ : Lab} (hℓ : ∀ i ∈ C, ℓs i = ℓ) (g : ∀ i, B i) :
    TranslateOn (slice C g) fun Δ =>
      T (C₀ + ∑ i, if γ i (Δ i) = 1 then ℓs i else 0) + if ∑ i, γ i (Δ i) = 1 then cm else 0 := by
  let β : (∀ i, B i) →+ ZMod 2 := ∑ i ∈ C, (γ i).comp (Pi.evalAddMonoidHom B i)
  have hβ : ∀ Δ, β Δ = ∑ i ∈ C, γ i (Δ i) := fun Δ => by
    simp [β]
  refine translateOn_gate (slice C g) hR β T cm
    (C₀ + ∑ i ∈ Finset.univ \ C, if γ i (g i) = 1 then ℓs i else 0) ℓ
    (∑ i ∈ Finset.univ \ C, γ i (g i)) (fun Δ hΔ => ?_) (fun Δ hΔ => ?_)
    (fun Δ hΔ Δ₂ h₂ Δ₃ h₃ => slice_translate hΔ h₂ h₃)
  · have h1 : (∑ i, if γ i (Δ i) = 1 then ℓs i else 0) =
        (∑ i ∈ Finset.univ \ C, if γ i (g i) = 1 then ℓs i else 0) +
          ∑ i ∈ C, if γ i (Δ i) = 1 then ℓ else 0 := by
      rw [← Finset.sum_sdiff (Finset.subset_univ C)]
      congr 1
      · exact Finset.sum_congr rfl fun i hi => by rw [hΔ i (Finset.mem_sdiff.1 hi).2]
      · exact Finset.sum_congr rfl fun i hi => by rw [hℓ i hi]
    rw [h1, sum_ite_bit hLab, hβ]
    split_ifs
    · rw [add_assoc]
    · rw [add_zero]
  · rw [hβ, ← Finset.sum_sdiff (Finset.subset_univ C)]
    congr 1
    exact Finset.sum_congr rfl fun i hi => by rw [hΔ i (Finset.mem_sdiff.1 hi).2]

end Gate

/-- `AffineOn` from closure under translations and `TranslateOn` of the rows. -/
lemma affineOn_of_translateOn {F X : Type*} [Field F] [AddCommGroup X] {L : ℕ} {S : Set X}
    {Q : X → Fin L → F} {D : X → Fin 4 → F}
    (hS : ∀ Δ ∈ S, ∀ Δ₂ ∈ S, ∀ Δ₃ ∈ S, Δ + (Δ₃ - Δ₂) ∈ S) (hQ : TranslateOn S Q)
    (hD : TranslateOn S D) : AffineOn S Q D :=
  fun Δ hΔ Δ₂ h₂ Δ₃ h₃ => ⟨hS Δ hΔ Δ₂ h₂ Δ₃ h₃, hQ Δ hΔ Δ₂ h₂ Δ₃ h₃, hD Δ hΔ Δ₂ h₂ Δ₃ h₃⟩

/-! ## Extractors that only evaluate the check value (`pomfrit-lemmap-tight.md` §6.5)

A deterministic extractor with oracle access to a function `f : X → Y` is a decision tree. If the
functions `f_g` of a family differ from a base function `f₀` only on pairwise disjoint sets
`σ_g` (hidden slices), the extractor's output on `f_g` is its output on `f₀` for all but at most
`T` values of `g`, where `T` is the number of its queries on `f₀`. -/

section BlackBox

/-- A deterministic algorithm with oracle access to a function `X → Y` and output in `O`. -/
inductive DTree (X Y O : Type*) where
  | leaf : O → DTree X Y O
  | node : X → (Y → DTree X Y O) → DTree X Y O

variable {X Y O : Type*}

/-- The output on the oracle `f`. -/
def DTree.eval : DTree X Y O → (X → Y) → O
  | .leaf o, _ => o
  | .node x k, f => (k (f x)).eval f

/-- The queries made on the oracle `f`. -/
def DTree.queries : DTree X Y O → (X → Y) → List X
  | .leaf _, _ => []
  | .node x k, f => x :: (k (f x)).queries f

/-- Two oracles that agree on the queries made on the first give the same output. -/
lemma DTree.eval_congr (t : DTree X Y O) {f f' : X → Y} (h : ∀ x ∈ t.queries f, f x = f' x) :
    t.eval f = t.eval f' := by
  induction t with
  | leaf o => rfl
  | node x k ih =>
    have hx : f x = f' x := h x (by simp [DTree.queries])
    simp only [DTree.eval]
    rw [← hx]
    exact ih (f x) fun y hy => h y (by simp [DTree.queries, hy])

open Classical in
/-- **Black-box extractors do not find hidden slices.** If `f g` agrees with `f₀` outside `σ g`
and the sets `σ g` are pairwise disjoint, an algorithm that makes `T` queries on `f₀` gives its
output on `f₀` for all but at most `T` of the `g`. -/
theorem DTree.card_detect_le {Γ : Type*} [Fintype Γ] (t : DTree X Y O) (f₀ : X → Y)
    (f : Γ → X → Y) (σ : Γ → Set X) (hσ : ∀ g x, x ∉ σ g → f g x = f₀ x)
    (hdisj : ∀ g g' x, x ∈ σ g → x ∈ σ g' → g = g') :
    #{g : Γ | t.eval (f g) ≠ t.eval f₀} ≤ (t.queries f₀).length := by
  have hsub : ({g : Γ | t.eval (f g) ≠ t.eval f₀} : Finset Γ) ⊆
      (t.queries f₀).toFinset.biUnion fun x => {g : Γ | x ∈ σ g} := by
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    by_contra hnot
    refine hg (t.eval_congr fun x hx => ?_).symm
    by_contra hne
    refine hnot (Finset.mem_biUnion.2 ⟨x, List.mem_toFinset.2 hx, ?_⟩)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra hxσ
    exact hne (hσ g x hxσ).symm
  calc #{g : Γ | t.eval (f g) ≠ t.eval f₀}
      ≤ #((t.queries f₀).toFinset.biUnion fun x => ({g : Γ | x ∈ σ g} : Finset Γ)) :=
        Finset.card_le_card hsub
    _ ≤ ∑ x ∈ (t.queries f₀).toFinset, #({g : Γ | x ∈ σ g} : Finset Γ) := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ (t.queries f₀).toFinset, 1 := Finset.sum_le_sum fun x _ =>
        Finset.card_le_one.2 fun g hg g' hg' => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg hg'
          exact hdisj g g' x hg hg'
    _ = #(t.queries f₀).toFinset := by simp
    _ ≤ (t.queries f₀).length := List.toFinset_card_le _

end BlackBox

end VoleMole.Seed
