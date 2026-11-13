import VoleMole.Protocols.PomFRIT
import VoleMole.Verifier.Bridge.ChainRelations

/-!
# Lemma P, the deterministic step: extraction into the widest prefix group

`lean/docs/security/pomfrit.md` §5. The first-phase extractor `E₁` groups a set `S` of trees (the
fully alive ones) by the prefix of their candidates and picks the group of largest total challenge
width (`majP`; ties broken by the least tree index). This file proves, per chain, that if every tree
outside `S` is fixed on the accepting set, then **either some tree of `S` in that widest group has
a candidate that satisfies the relation, or at most `2⁵⁷` admissible `chal3` are accepted**
(`extract_or_major`, generic; `pomfritT_extract_major_chain`, for the executable verifier's PomFRIT
chains with any target). This is `extract_or_few` with Lemma P's step 6 added: the free tree holds
`u*`; the trees outside `u*`'s prefix group are fixed (`fixed_of_prefix_ne`); if that group is not
the widest one, its width is at most 57 (`minority_card_le`).

* `grpW S p ρ`: the total width of the trees of `S` with prefix `ρ`.
* `majTree S p`, `majP S p`: the least tree of a widest group, and its prefix (`none` iff `S = ∅`).
* `majP_spec`: every group is at most as wide as the chosen one.

No `sorry`, no `axiom`.
-/

open Finset

namespace VoleMole.PomFRIT

open VoleMole.SeedExtraction

/-! ## The widest prefix group -/

section Major

variable {P : Type*} [DecidableEq P]

/-- The total challenge width of the trees of `S` whose prefix is `ρ`. -/
def grpW (S : Finset (Fin 17)) (p : Fin 17 → P) (ρ : P) : ℕ :=
  ∑ i ∈ S.filter (fun i => p i = ρ), width i

/-- The trees of `S` whose group is a widest one. -/
def majSet (S : Finset (Fin 17)) (p : Fin 17 → P) : Finset (Fin 17) :=
  S.filter fun i => ∀ i' ∈ S, grpW S p (p i') ≤ grpW S p (p i)

/-- The least tree of a widest group (`none` iff `S` is empty). -/
def majTree (S : Finset (Fin 17)) (p : Fin 17 → P) : Option (Fin 17) :=
  if h : (majSet S p).Nonempty then some ((majSet S p).min' h) else none

/-- **`E₁`'s choice**: the prefix of a widest group, ties broken by the least tree index. -/
def majP (S : Finset (Fin 17)) (p : Fin 17 → P) : Option P := (majTree S p).map p

lemma majSet_nonempty {S : Finset (Fin 17)} (hS : S.Nonempty) (p : Fin 17 → P) :
    (majSet S p).Nonempty := by
  obtain ⟨i, hi, hmax⟩ := S.exists_max_image (fun i => grpW S p (p i)) hS
  exact ⟨i, mem_filter.2 ⟨hi, hmax⟩⟩

/-- **The chosen group is a widest one**: for a tree `i₀ ∈ S`, `majP` is some prefix `ρ` of a tree
of `S` with `grpW (p i₀) ≤ grpW ρ`. -/
theorem majP_spec {S : Finset (Fin 17)} {i₀ : Fin 17} (hi₀ : i₀ ∈ S) (p : Fin 17 → P) :
    ∃ ρ, majP S p = some ρ ∧ grpW S p (p i₀) ≤ grpW S p ρ := by
  have hne := majSet_nonempty ⟨i₀, hi₀⟩ p
  have hmem : (majSet S p).min' hne ∈ majSet S p := Finset.min'_mem _ hne
  refine ⟨p ((majSet S p).min' hne), by simp [majP, majTree, hne], ?_⟩
  exact (mem_filter.1 hmem).2 i₀ hi₀

lemma majP_eq_none_iff {S : Finset (Fin 17)} (p : Fin 17 → P) : majP S p = none ↔ S = ∅ := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hne
    obtain ⟨ρ, hρ, -⟩ := majP_spec hi p
    rw [hρ] at h
    cases h
  · rintro rfl
    simp [majP, majTree, majSet]

/-- `majP` reads `p` on `S` only. -/
lemma majP_congr {S : Finset (Fin 17)} {p p' : Fin 17 → P} (h : ∀ i ∈ S, p i = p' i) :
    majP S p = majP S p' := by
  have hg : ∀ ρ, grpW S p ρ = grpW S p' ρ := fun ρ => by
    unfold grpW
    congr 1
    exact Finset.filter_congr fun i hi => by rw [h i hi]
  have hs : majSet S p = majSet S p' := by
    unfold majSet
    refine Finset.filter_congr fun i hi => ?_
    refine forall₂_congr fun i' hi' => ?_
    rw [hg, hg, h i hi, h i' hi']
  unfold majP majTree
  rw [hs]
  by_cases hne : (majSet S p').Nonempty
  · have hmem : (majSet S p').min' hne ∈ S := (mem_filter.1 (Finset.min'_mem _ hne)).1
    simp [hne, h _ hmem]
  · simp [hne]

/-- Two different prefixes have disjoint groups. -/
lemma disjoint_groups (S : Finset (Fin 17)) (p : Fin 17 → P) {ρ ρ' : P} (h : ρ ≠ ρ') :
    Disjoint (S.filter fun i => p i = ρ) (S.filter fun i => p i = ρ') :=
  Finset.disjoint_filter.2 fun _ _ h1 h2 => h (h1.symm.trans h2)

end Major

/-! ## Extraction into the widest group (generic) -/

section Generic

variable {F : Type*} [Field F] [CharP F 2] [DecidableEq F]
variable {B : Fin 17 → Type*} [∀ i, AddCommGroup (B i)] [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]
variable {P : Type*} [DecidableEq P]

open VoleMole.EndToEnd in
/-- **Lemma P, per chain (generic).** With trees of `2^{width i}` challenges, Claim 4's hypotheses
on the set `S` (every tree outside `S` fixed), Claim 3 (QuickSilver, degree `d ≤ 2^57`) and Claim 1:
either some tree of `S` has a candidate satisfying `Wit` **and lies in the widest group** of `S` by
the prefix `pf` of the candidates, or at most `2⁵⁷` admissible `chal3` are accepted. -/
theorem extract_or_major {Ch : Type*} {ℓ d : ℕ} (hd : 1 ≤ d) (hd57 : d ≤ 2 ^ 57)
    (hB : ∀ i, Fintype.card (B i) = 2 ^ width i)
    {e : (∀ i, B i) →+ F} {A : Finset (∀ i, B i)} {S : Finset (Fin 17)} {u : Fin 17 → Fin ℓ → Bool}
    {Q : Fin ℓ → (∀ i, B i) → F} {uStar : Fin ℓ → F}
    (hK : Claim4Hyp e (A : Set (∀ k, B k)) S u Q uStar) (dc : Fin ℓ → Bool)
    (cs : Arith.System F) (hdeg : ∀ x ∈ cs, x.degree ≤ d) (Wit : (ℕ → F) → Prop)
    (hWbits : ∀ w, Wit w → ∀ j < ℓ, w j = 0 ∨ w j = 1)
    (χ : Fin cs.length → F) (R : Polynomial F) (hR : R.natDegree ≤ d - 1)
    (hacc : ∀ Δ ∈ A, qsCheck cs d χ (macs e Q dc Δ) (e Δ) + R.eval (e Δ) = 0)
    (hQS : ¬cs.Holds (extW (uStar + fun j => bit (dc j))) →
      ∑ k, χ k * valVec cs (extW (uStar + fun j => bit (dc j))) k ≠ 0)
    (hcomb : cs.Holds (extW (uStar + fun j => bit (dc j))) →
      Wit (extW (uStar + fun j => bit (dc j))))
    (pf : (ℕ → F) → P)
    (Z : Finset Ch) (δ : Ch → ∀ i, B i) (hδ : Set.InjOn δ Z) (acc : Ch → Prop)
    [DecidablePred acc] (hclaim1 : ∀ x ∈ Z, acc x → δ x ∈ A) :
    (∃ i ∈ S, Wit (candidate u dc i) ∧
        majP S (fun i => pf (candidate u dc i)) = some (pf (candidate u dc i))) ∨
      #{x ∈ Z | acc x} ≤ 2 ^ 57 := by
  classical
  have hcard : #{x ∈ Z | acc x} ≤ A.card := by
    refine Finset.card_le_card_of_injOn δ (fun x hx => ?_) (hδ.mono fun x hx => ?_)
    · have hx' := Finset.mem_filter.1 hx
      exact hclaim1 x hx'.1 hx'.2
    · exact (Finset.mem_filter.1 hx).1
  have hclaim3 : Wit (extW (uStar + fun j => bit (dc j))) ∨ A.card ≤ d :=
    (claim3_of_system hd hK.lift_inj (fun j => hK.consistent j) dc cs hdeg χ R hR
      (fun Δ hΔ => hacc Δ hΔ) hQS).imp_left hcomb
  rcases hclaim3 with hW | hA
  swap
  · exact Or.inr (hcard.trans (hA.trans hd57))
  have hbits : ∀ j, uStar j = 0 ∨ uStar j = 1 := by
    refine Seed.bits_of_bit_constraints (uStar + fun j => bit (dc j)) uStar (fun j => bit (dc j))
      (fun j => ?_) (fun j => by cases dc j <;> simp [bit]) rfl
    have := hWbits _ hW j j.isLt
    simp only [extW, j.isLt, dite_true] at this
    rcases this with h | h <;> simp [h, CharTwo.add_self_eq_zero]
  by_cases hfix : ∀ i, IsFixed (A : Set (∀ k, B k)) i
  · exact Or.inr (hcard.trans ((card_le_one_of_all_fixed hfix).trans (by norm_num)))
  push Not at hfix
  obtain ⟨i₀, hi₀⟩ := hfix
  obtain ⟨hk₀, hu₀⟩ := free_tree_holds_witness hK hbits hi₀
  have hcand₀ : candidate u dc i₀ = extW (uStar + fun j => bit (dc j)) := by
    unfold candidate
    congr 1
    funext j
    simp [hu₀ j]
  set p : Fin 17 → P := fun i => pf (candidate u dc i)
  obtain ⟨ρ, hρ, hle⟩ := majP_spec hk₀ p
  by_cases hmaj : p i₀ = ρ
  · exact Or.inl ⟨i₀, hk₀, hcand₀ ▸ hW, by rw [hρ, ← hmaj]⟩
  -- `u*`'s group is not the widest: every tree outside it is fixed, and it is a minority.
  right
  refine hcard.trans (minority_card_le hB A (S.filter fun i => p i = p i₀)
    (S.filter fun i => p i = ρ) (disjoint_groups S p hmaj) hle fun i hi => ?_)
  by_cases hiS : i ∈ S
  · have hne : p i ≠ p i₀ := fun h => hi (mem_filter.2 ⟨hiS, h⟩)
    have hcne : candidate u dc i ≠ candidate u dc i₀ := fun h => hne (by simp only [p]; rw [h])
    obtain ⟨j, hj⟩ : ∃ j : Fin ℓ, u i j ≠ u i₀ j := by
      by_contra hall
      push Not at hall
      exact hcne (by unfold candidate; congr 1; funext j; rw [hall j])
    refine fixed_of_prefix_ne hK hbits (j := j) ?_
    rw [← hu₀ j]
    intro h
    apply hj
    cases h1 : u i j <;> cases h2 : u i₀ j <;> simp_all [bit]
  · exact hK.unknown_fixed i hiS

end Generic

/-! ## PomFRIT's chains -/

section Chain

open VoleMole.Arith VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.EndToEnd

variable [HasPrg]

omit [HasPrg] in
lemma card_block (i : Fin BAVC.tau) : Fintype.card (Fin (BAVC.kOf i) → ZMod 2) = 2 ^ width i := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  congr 1
  fin_cases i <;> rfl

set_option maxRecDepth 8000 in
/-- **Lemma P at a chain of the executable verifier** (`pomfritRedeem_extract_chain` with the
widest-group conclusion and `2⁵⁷`): for a statement with PomFRIT's parameters whose constraint
evaluator is PomFRIT's system at a target `h` and a combination `l`, with every tree outside `S`
fixed on `A`: some tree of `S` has a candidate encoding `(ρ, σ)` with `P(σ) = h + ρ` and lies in the
widest group of `S` by the prefix `pf`, or at most `2⁵⁷` admissible `chal3` are accepted. -/
theorem pomfritT_extract_major_chain {Ch : Type*} {P : Type*} [DecidableEq P] (pk : UovPk)
    (st : Statement) (lr : Bool) (hp : st.params = pomfritParams lr) (ch : Chain)
    (h : Fin 45 → GF256) (l : Fin 45 → GF128)
    (hvals : ∀ x, ch.vals x =
      (PomFRIT.pomfritRedeemSystem beta GF256.toBits 119 45 pk.map h l).values x)
    {A : Finset Blocks} (hA : ∀ Δ ∈ A, ch.OnChain st CrtGen.tables Δ) {Sb : Set Blocks}
    (hAS : (A : Set Blocks) ⊆ Sb)
    (hkos : Seed.KOSGood ch.kosCh Sb (lift CrtGen.tables) (ch.kosQ st CrtGen.tables)
      (ch.kosD st CrtGen.tables))
    {S : Finset (Fin BAVC.tau)} (hL2 : ∀ i ∉ S, IsFixed (A : Set Blocks) i)
    (hQS : 2 ≤ A.card → ∀ uStar, (∀ j, ∃ v, ∀ Δ ∈ A,
        ch.Qw st CrtGen.tables j Δ = v + uStar j * lift CrtGen.tables Δ) →
      ¬(PomFRIT.pomfritRedeemSystem beta GF256.toBits 119 45 pk.map h l).Holds
        (wStar uStar (ch.dc st)) →
      Seed.zkHash _ (gfOfBytes ch.chal2 0) (gfOfBytes ch.chal2 16) (gfOfBytes ch.chal2 32)
        ⟨W128.word ch.chal2 48, 0⟩
        (valVec (PomFRIT.pomfritRedeemSystem beta GF256.toBits 119 45 pk.map h l)
          (wStar uStar (ch.dc st))) ≠ 0)
    (hcomb : 2 ≤ A.card → ∀ uStar, (∀ j, ∃ v, ∀ Δ ∈ A,
        ch.Qw st CrtGen.tables j Δ = v + uStar j * lift CrtGen.tables Δ) →
      (PomFRIT.pomfritRedeemSystem beta GF256.toBits 119 45 pk.map h l).Holds
        (wStar uStar (ch.dc st)) →
      pomfritWit GF256.ofBits 119 45 pk.map h (wStar uStar (ch.dc st)))
    (pf : (ℕ → GF128) → P)
    (Z : Finset Ch) (δ : Ch → Blocks) (hδ : Set.InjOn δ Z) (acc : Ch → Prop) [DecidablePred acc]
    (hclaim1 : ∀ x ∈ Z, acc x → δ x ∈ A) :
    (∃ i ∈ S, pomfritWit GF256.ofBits 119 45 pk.map h
        (candidate (F := GF128) (ch.u st) (ch.dc st) i) ∧
        majP S (fun i => pf (candidate (F := GF128) (ch.u st) (ch.dc st) i)) =
          some (pf (candidate (F := GF128) (ch.u st) (ch.dc st) i))) ∨
      #{x ∈ Z | acc x} ≤ 2 ^ 57 := by
  by_cases hA1 : A.card ≤ 1
  · exact Or.inr (few_of_card_le_one hA1 Z δ hδ acc hclaim1 (by norm_num))
  obtain ⟨p, d, dl, b1, b2, ie, cb, v⟩ := st
  dsimp only at hp
  subst hp
  obtain ⟨uStar, R, hR, hK, hacc⟩ := chain_claim4 liftInvOk_tables _ ch _ hvals
    (PomFRIT.degree_pomfritRedeemSystem _ _ _ _ _ _ _) hA hAS hkos hL2
  exact extract_or_major (d := 2) (by norm_num) (by norm_num) card_block hK _ _
    (PomFRIT.degree_pomfritRedeemSystem _ _ _ _ _ _ _) (pomfritWit GF256.ofBits 119 45 pk.map h)
    (fun w hw => bits_of_exists_bitF w hw) _ R hR hacc
    (fun hh => by rw [← Seed.zkHash_eq_sum]; exact hQS (by omega) uStar hK.consistent hh)
    (hcomb (by omega) uStar hK.consistent) pf Z δ hδ acc hclaim1

end Chain

end VoleMole.PomFRIT
