import VoleMole.Arith.UOV

/-!
# PomFRIT redeem: `P(s) = h + r` (`src/pomfrit/redeem.hpp`)

An executable model of `pomfrit::detail::RedeemRelation::constraints`
(`src/pomfrit/redeem.hpp:113-143`), with completeness and soundness proofs against the relation
the protocol proofs use (`lean/docs/security/pomfrit.md:91`):

    R_PomFRIT((pk, h), (r, s))  ⇔  P_pk(s) = h ⊕ r.

`h` is the target `hash_to_target(pk, sig, chal1, msg)` (`src/pomfrit/pomfrit.cpp:96-111`), `r` the
target mask squeezed by the Client (`pomfrit.cpp:149-161`), and the Issuer signs `t = h ⊕ r`
(`pomfrit.cpp:172-176`). Addition in GF(256) is XOR, so in the model, where `K` is an abstract
GF(256) with its own `+`, the relation reads `P(σ)_k = h_k + ρ_k` (`pomfritRel`). On the concrete
GF(256) this is literally byte-wise XOR. The constraint checks `l(P(s)) + l(r) + l(h) = 0` in
GF(2¹²⁸); `ι` is additive (`IsEmbedding.map_add`, L7-uov.md Lemma 1(b)), so
`ι(P_k) + ι(ρ_k) + ι(h_k) = ι(P_k + (h_k + ρ_k))` and injectivity of `ι` gives the relation. No
characteristic hypothesis on `K` is needed: only `ι(x) + ι(x) = 0` in `F` (char 2) is used.

This mechanizes §4 of `lean/docs/extraction/L7-uov.md` (up to its Claim 2b: `publicMap` is *defined* by the
`for_each_monomial` layout; see `VoleMole/Arith/UOV.lean`).

## Model

* Witness layout (`redeem.hpp:42-45`): `r` = bytes `[WIT_OFF_R, WIT_OFF_R + M) = [0, M)`, `s` =
  bytes `[WIT_OFF_S, WIT_OFF_S + N) = [M, M + N)`; `8(M + N)` witness bits.
* Constraints, in `add_constraint` order (`REDEEM_NUM_CONSTRAINTS = 8(M+N) + 1`, `:49-50`):
  1. `qs_add_bit_constraint(get_witness_bit(i))` for `i < 8(M+N)` (`:121-123`), i.e.
     `bitConstraint (wit i)` (`src/qs_bit.hpp:75-77`);
  2. `lp + qs_2(lr + lh)` (`:142`), with
     - `lp = qs_eval_combined_public_map(pk, s, l)`, `s_i = load_witness_8_bits_and_combine(8(M+i))`
       (`:127-131`): `evalCombinedPublicMap β toBits N M pk (byteLoad β (M + ·)) l`;
     - `lr = qs_1(poly1(0)); lr += l.coeff(k) * r_k` with `r_k` the byte at `WIT_OFF_R + k`
       (`:133, 136-138`): `linComb l (byteLoad β (0 + ·))`;
     - `lh = 0; lh += l.coeff(k) * embed(h[k])` (`:134, 139-140`), a public constant:
       `combineVec β toBits l h`;
     - `qs_2(·)` (degree lift) is the identity on values (L7-uov.md §0).
  The witness loads have no side effects, so interleaving the `r_k` loads with the `lh` updates
  does not affect the expressions.
* `l : Fin M → F` is `Combination(chal2, POMFRIT_COMBINE_DST)` (`:126`), passed as an argument.

## Generator interface (for the differential tests)

```
pomfritRedeemSystem {F K} [Add F] [Mul F] [Zero F] [One F]
  (β : Fin 8 → F) (toBits : K → Fin 8 → Bool) (N M : ℕ) (pk : ℕ → K) (h : Fin M → K)
  (l : Fin M → F) : System F
```
* `β`: `β 0 = 1`, `β b = gf8_in_gf128[b-1]`; `toBits`: byte ↦ bits, LSB first.
* `N = uov::N`, `M = uov::M`; `pk m` = byte `m` of `PublicKeyAccess::expanded(pk)`.
* `h`: the instance target `x.h` (bytes); `l k = Combination::coeff(k)` (from `chal2`).
* Witness: bit `i` = bit `i % 8` of witness byte `i / 8`, bytes `r ‖ s` (`8(M+N)` bits).
* Output: `8(M+N)` bit constraints (index `i` ↔ witness bit `i`), then the output constraint
  (`outputConstraint`), matching the order of the C++ `add_constraint` calls.

## Main results

* `pomfritRedeemSystem_length`: `8(M+N) + 1` constraints; `degree_pomfritRedeemSystem`: degree ≤ 2.
* `pomfrit_holds_iff`: on a bit vector, all constraints hold iff
  `Σ_k l_k (ι(P(σ)_k) + ι(h_k + ρ_k)) = 0`.
* `pomfrit_complete`: an honest witness (`P(σ) = h + ρ`) satisfies every constraint, for every `l`.
* `pomfrit_sound`: if the constraints hold at any `w ∈ F^ℓ`, every witness bit is a bit, and the
  decoded `(ρ, σ)` satisfy the combined equation.
* `pomfrit_rel_of_forall`: if the combined equation holds for all `l`, `(ρ, σ)` is a witness.
* `pomfrit_card_bad` / `pomfrit_bad_prob`: if `(ρ, σ)` is not a witness, a `1/|F|` fraction of `l`
  passes the combined equation (via `uov_card_bad` with `t = h + ρ`).
* `pomfrit_sound_card`: end to end, for committed values `w` fixed before `l`: either `w` is a bit
  vector encoding a witness, or `#{l | constraints hold at w} · |F| ≤ |F^M|`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace VoleMole.Arith.PomFRIT

open UOV

/-! ## The generator -/

section Generator

variable {F K : Type*} [Add F] [Mul F] [Zero F] [One F]

/-- `WIT_OFF_R` (`redeem.hpp:42`). -/
def witOffR : ℕ := 0

/-- `WIT_OFF_S = WIT_OFF_R + M` (`redeem.hpp:43`). -/
def witOffS (M : ℕ) : ℕ := witOffR + M

/-- `REDEEM_WITNESS_BITS = 8 (M + N)` (`redeem.hpp:44-45`). -/
def witnessBits (N M : ℕ) : ℕ := 8 * (witOffS M + N)

/-- The output constraint `lp + qs_2(lr + lh)` (`redeem.hpp:125-142`). -/
def outputConstraint (β : Fin 8 → F) (toBits : K → Fin 8 → Bool) (N M : ℕ) (pk : ℕ → K)
    (h : Fin M → K) (l : Fin M → F) : Expr F :=
  evalCombinedPublicMap β toBits N M pk (fun i => byteLoad β (witOffS M + i)) l +
    (linComb l (fun k => byteLoad β (witOffR + k)) + Expr.const (combineVec β toBits l h))

/-- `RedeemRelation::constraints(qs, {pk, h}, chal2)` (`redeem.hpp:113-143`): the bit constraints
on all `8(M+N)` witness bits, then the output constraint.

Arguments: the embedding constants `β`, the byte decomposition `toBits` of GF(256), the UOV sizes
`N`, `M`, the expanded public key `pk` (`PublicKeyAccess::expanded`), the target `h`, and the
combination coefficients `l`. -/
def pomfritRedeemSystem (β : Fin 8 → F) (toBits : K → Fin 8 → Bool) (N M : ℕ) (pk : ℕ → K)
    (h : Fin M → K) (l : Fin M → F) : System F :=
  (List.range (witnessBits N M)).map (fun i => bitConstraint (Expr.wit i)) ++
    [outputConstraint β toBits N M pk h l]

theorem pomfritRedeemSystem_length (β : Fin 8 → F) (toBits : K → Fin 8 → Bool) (N M : ℕ)
    (pk : ℕ → K) (h : Fin M → K) (l : Fin M → F) :
    (pomfritRedeemSystem β toBits N M pk h l).length = 8 * (M + N) + 1 := by
  simp [pomfritRedeemSystem, witnessBits, witOffS, witOffR]

theorem degree_linComb {M : ℕ} (l : Fin M → F) (T : Fin M → Expr F) (hT : ∀ k, (T k).degree ≤ 1) :
    (linComb l T).degree ≤ 1 := by
  have : ∀ (L : List (Fin M)) (a : Expr F), a.degree ≤ 1 →
      (L.foldl (fun acc k => acc + Expr.const (l k) * T k) a).degree ≤ 1 := by
    intro L
    induction L with
    | nil => exact fun _ h => h
    | cons k L ih =>
      intro a ha
      refine ih _ ?_
      have := hT k
      simp only [Expr.degree] at *
      omega
  exact this _ _ (by simp [Expr.degree])

/-- Every constraint has degree `≤ 2` (`REDEEM_QS_DEGREE`, `redeem.hpp:47`). -/
theorem degree_pomfritRedeemSystem (β : Fin 8 → F) (toBits : K → Fin 8 → Bool) (N M : ℕ)
    (pk : ℕ → K) (h : Fin M → K) (l : Fin M → F) :
    ∀ e ∈ pomfritRedeemSystem β toBits N M pk h l, e.degree ≤ 2 := by
  intro e he
  simp only [pomfritRedeemSystem, List.mem_append, List.mem_map, List.mem_singleton] at he
  rcases he with ⟨i, -, rfl⟩ | rfl
  · simp [bitConstraint, degree_mul, Expr.degree]
  · have h1 := degree_evalCombinedPublicMap β toBits N M pk
      (fun i => byteLoad β (witOffS M + i)) l (fun i => (degree_byteLoad β _).le)
    have h2 := degree_linComb l (fun k => byteLoad β (witOffR + k))
      (fun k => (degree_byteLoad β _).le)
    simp only [outputConstraint, degree_add, Expr.degree] at *
    omega

end Generator

/-! ## The relation -/

section Relation

variable {K : Type*} [Add K] [Mul K] [Zero K]

/-- `R_PomFRIT((pk, h), (ρ, σ)) ⇔ P_pk(σ) = h + ρ` (`lean/docs/security/pomfrit.md:91`; GF(256) addition is
XOR, `pomfrit.cpp:174-175`). -/
def pomfritRel (N M : ℕ) (pk : ℕ → K) (h : Fin M → K) (ρ : Fin M → K) (σ : ℕ → K) : Prop :=
  publicMap N M pk σ = fun k => h k + ρ k

/-- The decoded mask `ρ_k` = witness byte `WIT_OFF_R + k`. -/
def decodeR (ofByte : (Fin 8 → Bool) → K) (w : ℕ → Bool) (M : ℕ) : Fin M → K :=
  fun k => decode ofByte w witOffR k

/-- The decoded preimage `σ_i` = witness byte `WIT_OFF_S + i`. -/
def decodeS (ofByte : (Fin 8 → Bool) → K) (w : ℕ → Bool) (M : ℕ) : ℕ → K :=
  decode ofByte w (witOffS M)

end Relation

/-! ## Values, completeness, soundness -/

section Proofs

variable {F K : Type*} [Field F] [CharP F 2] [Add K] [Mul K] [Zero K]
variable {β : Fin 8 → F} {toBits : K → Fin 8 → Bool} {ofByte : (Fin 8 → Bool) → K}

/-- A byte loaded from committed values that are bits on its 8 positions is `ι` of the byte. -/
theorem eval_byteLoad_of_bits (hι : IsEmbedding β toBits ofByte) (o i : ℕ) (w : ℕ → F)
    (wb : ℕ → Bool) (hw : ∀ b < 8, w (8 * (o + i) + b) = bitF (wb (8 * (o + i) + b))) :
    (byteLoad β (o + i)).eval w = embed β (toBits (decode ofByte wb o i)) := by
  rw [← eval_byteLoad_bits hι wb o i, eval_byteLoad, eval_byteLoad]
  exact Finset.sum_congr rfl fun b _ => by rw [hw b b.isLt]; rfl

/-- The output constraint's value at committed values that are bits on all `8(M+N)` witness bits:
`Σ_k l_k (ι(P(σ)_k) + ι(h_k + ρ_k))` (L7-uov.md §4, `A_k = ι(P_k(σ) + ρ_k + h_k)`). -/
theorem eval_outputConstraint_of_bits (hι : IsEmbedding β toBits ofByte) (N M : ℕ) (pk : ℕ → K)
    (h : Fin M → K) (l : Fin M → F) (w : ℕ → F) (wb : ℕ → Bool)
    (hw : ∀ i < witnessBits N M, w i = bitF (wb i)) :
    (outputConstraint β toBits N M pk h l).eval w =
      ∑ k, l k * (embed β (toBits (publicMap N M pk (decodeS ofByte wb M) k)) +
        embed β (toBits (h k + decodeR ofByte wb M k))) := by
  simp only [witnessBits, witOffS, witOffR, zero_add] at hw
  have hs : ∀ n < 8 * N, w (8 * witOffS M + n) = bitF (wb (8 * witOffS M + n)) := fun n hn =>
    hw _ (by simp only [witOffS, witOffR]; omega)
  have hr : ∀ k : Fin M, (byteLoad β (witOffR + k)).eval w =
      embed β (toBits (decodeR ofByte wb M k)) := fun k =>
    eval_byteLoad_of_bits hι _ _ w wb fun b hb => hw _ (by simp only [witOffR]; omega)
  simp only [outputConstraint, Expr.eval_add, Expr.eval_const,
    eval_evalCombinedPublicMap_of_bits hι N M pk l _ w wb hs, eval_linComb, hr, combineVec_eq,
    hι.map_add, decodeS]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem bits_holds (N M : ℕ) (w : ℕ → Bool) :
    ∀ e ∈ (List.range (witnessBits N M)).map (fun i => bitConstraint (Expr.wit i)),
      e.eval (ofBits w : ℕ → F) = 0 := by
  simp only [List.mem_map]
  rintro e ⟨n, -, rfl⟩
  exact bitConstraint_bits w _

/-- On a bit vector, every constraint holds iff `Σ_k l_k (ι(P(σ)_k) + ι(h_k + ρ_k)) = 0`. -/
theorem pomfrit_holds_iff (hι : IsEmbedding β toBits ofByte) (N M : ℕ) (pk : ℕ → K)
    (h : Fin M → K) (l : Fin M → F) (w : ℕ → Bool) :
    (pomfritRedeemSystem β toBits N M pk h l).Holds (ofBits w) ↔
      ∑ k, l k * (embed β (toBits (publicMap N M pk (decodeS ofByte w M) k)) +
        embed β (toBits (h k + decodeR ofByte w M k))) = 0 := by
  rw [pomfritRedeemSystem, System.holds_append,
    ← eval_outputConstraint_of_bits hι N M pk h l (ofBits w) w fun _ _ => rfl]
  simp only [System.Holds, List.mem_singleton, forall_eq]
  exact ⟨fun h => h.2, fun h => ⟨bits_holds N M w, h⟩⟩

/-- **Completeness.** If the witness bits encode `(ρ, σ)` with `P(σ) = h + ρ`, every constraint
holds, for every choice of `l`. -/
theorem pomfrit_complete (hι : IsEmbedding β toBits ofByte) (N M : ℕ) (pk : ℕ → K)
    (h : Fin M → K) (l : Fin M → F) (w : ℕ → Bool)
    (hrel : pomfritRel N M pk h (decodeR ofByte w M) (decodeS ofByte w M)) :
    (pomfritRedeemSystem β toBits N M pk h l).Holds (ofBits w) := by
  rw [pomfrit_holds_iff hι, hrel]
  simp [CharTwo.add_self_eq_zero]

/-- **Soundness (deterministic).** If the constraints hold at any committed values `w ∈ F^ℓ`, then
every witness bit is a bit (`wb i = (w i = 1)`, independent of `l`), and the decoded `(ρ, σ)`
satisfy the combined equation. -/
theorem pomfrit_sound [DecidableEq F] (hι : IsEmbedding β toBits ofByte) (N M : ℕ) (pk : ℕ → K)
    (h : Fin M → K) (l : Fin M → F) (w : ℕ → F)
    (hw : (pomfritRedeemSystem β toBits N M pk h l).Holds w) :
    (∀ i < witnessBits N M, w i = bitF (decide (w i = 1))) ∧
      ∑ k, l k * (embed β (toBits (publicMap N M pk (decodeS ofByte (fun i => decide (w i = 1)) M) k)) +
        embed β (toBits (h k + decodeR ofByte (fun i => decide (w i = 1)) M k))) = 0 := by
  rw [pomfritRedeemSystem, System.holds_append] at hw
  obtain ⟨hb, ho⟩ := hw
  have hbit : ∀ i < witnessBits N M, w i = bitF (decide (w i = 1)) := fun i hi =>
    eq_bitF_of_bitConstraint (hb _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))
  refine ⟨hbit, ?_⟩
  rw [← eval_outputConstraint_of_bits hι N M pk h l w _ hbit]
  exact ho _ (List.mem_singleton_self _)

/-- If the combined equation holds for every `l`, then `(ρ, σ)` is a witness. -/
theorem pomfrit_rel_of_forall (hι : IsEmbedding β toBits ofByte) {N M : ℕ} {pk : ℕ → K}
    {h ρ : Fin M → K} {σ : ℕ → K}
    (hall : ∀ l : Fin M → F, ∑ k, l k * (embed β (toBits (publicMap N M pk σ k)) +
      embed β (toBits (h k + ρ k))) = 0) :
    pomfritRel N M pk h ρ σ :=
  publicMap_eq_of_forall (t := fun k => h k + ρ k) hι hall

/-- **The combination step.** If `(ρ, σ)` is not a witness, exactly a `1/|F|` fraction of the
coefficient vectors `l` passes the combined equation. -/
theorem pomfrit_card_bad [Fintype F] [DecidableEq F] (hι : IsEmbedding β toBits ofByte)
    {N M : ℕ} {pk : ℕ → K} {h ρ : Fin M → K} {σ : ℕ → K} (hrel : ¬ pomfritRel N M pk h ρ σ) :
    #{l : Fin M → F | ∑ k, l k * (embed β (toBits (publicMap N M pk σ k)) +
      embed β (toBits (h k + ρ k))) = 0} * Fintype.card F = Fintype.card (Fin M → F) :=
  uov_card_bad (t := fun k => h k + ρ k) hι hrel

theorem pomfrit_bad_prob [Fintype F] [DecidableEq F] (hι : IsEmbedding β toBits ofByte)
    {N M : ℕ} {pk : ℕ → K} {h ρ : Fin M → K} {σ : ℕ → K} (hrel : ¬ pomfritRel N M pk h ρ σ) :
    (#{l : Fin M → F | ∑ k, l k * (embed β (toBits (publicMap N M pk σ k)) +
      embed β (toBits (h k + ρ k))) = 0} : ℝ) / Fintype.card (Fin M → F) =
      (Fintype.card F : ℝ)⁻¹ :=
  uov_bad_prob (t := fun k => h k + ρ k) hι hrel

open Classical in
/-- **Soundness, end to end.** Fix the committed values `w ∈ F^ℓ` (and `pk`, `h`) before drawing
`l`. Either `w` is a bit vector on the `8(M+N)` witness bits whose bytes `(ρ, σ)` satisfy
`P(σ) = h + ρ`, or at most a `1/|F|` fraction of the `l` make every constraint hold. -/
theorem pomfrit_sound_card [Fintype F] [DecidableEq F] (hι : IsEmbedding β toBits ofByte)
    (N M : ℕ) (pk : ℕ → K) (h : Fin M → K) (w : ℕ → F) :
    (∃ wb : ℕ → Bool, (∀ i < witnessBits N M, w i = bitF (wb i)) ∧
        pomfritRel N M pk h (decodeR ofByte wb M) (decodeS ofByte wb M)) ∨
      #{l : Fin M → F | (pomfritRedeemSystem β toBits N M pk h l).Holds w} * Fintype.card F ≤
        Fintype.card (Fin M → F) := by
  set wb : ℕ → Bool := fun i => decide (w i = 1)
  by_cases hgood : (∀ i < witnessBits N M, w i = bitF (wb i)) ∧
      pomfritRel N M pk h (decodeR ofByte wb M) (decodeS ofByte wb M)
  · exact Or.inl ⟨wb, hgood⟩
  right
  by_cases hbit : ∀ i < witnessBits N M, w i = bitF (wb i)
  · have hrel : ¬ pomfritRel N M pk h (decodeR ofByte wb M) (decodeS ofByte wb M) :=
      fun hr => hgood ⟨hbit, hr⟩
    rw [← pomfrit_card_bad hι hrel]
    refine Nat.mul_le_mul_right _ (Finset.card_le_card fun l hl => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
    exact (pomfrit_sound hι N M pk h l w hl).2
  · have : #{l : Fin M → F | (pomfritRedeemSystem β toBits N M pk h l).Holds w} = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun l _ hl => hbit (pomfrit_sound hι N M pk h l w hl).1
    rw [this, zero_mul]
    exact Nat.zero_le _

end Proofs

end VoleMole.Arith.PomFRIT
