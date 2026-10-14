import VoleMole.Arith.PomFRIT
import VoleMole.Arith.Moussaka
import VoleMole.Arith.Ratatouille

/-!
# Degrees of the four Keccak-based systems

`extract_or_few` needs every constraint to have formal degree `≤ QS_DEGREE`. `Arith/PomFRIT.lean`
proves this for PomFRIT redeem (`degree_pomfritRedeemSystem`, `≤ 2`). This file proves `≤ 9`
(`MOUSSAKA_*_QS_DEGREE`, `RATATOUILLE_*_QS_DEGREE`) for the other four systems, from the Keccak
gadget's `qsKeccak_degree` (segments `≤ 9`, outputs `≤ 8`) and the UOV gadget's
`degree_evalCombinedPublicMap` (`≤ 2`). The largest non-Keccak degree is `8 + 1` for Moussaka
redeem's output constraint `lout + qs_lift(lq)` (`lout` reads Keccak outputs of degree 8 and `lq`
has degree 3).
-/

set_option linter.unusedSectionVars false

namespace VoleMole.EndToEnd.Degree

open VoleMole.Arith
open VoleMole.Arith.Keccak (qsKeccak qsInput qsByte qsKeccak_degree qsInput_degree)

variable {F K : Type*} [Field F]

theorem degree_add' (a b : Expr F) : (a + b).degree = max a.degree b.degree := rfl
theorem degree_mul' (a b : Expr F) : (a * b).degree = a.degree + b.degree := rfl

theorem degree_foldl_add {α : Type*} (f : α → Expr F) {D : ℕ} (hf : ∀ x, (f x).degree ≤ D) :
    ∀ (L : List α) (a : Expr F), a.degree ≤ D → (L.foldl (fun acc x => acc + f x) a).degree ≤ D
  | [], _, ha => ha
  | x :: L, a, ha => degree_foldl_add f hf L _ (by rw [degree_add']; exact max_le ha (hf x))

theorem degree_linComb {M D : ℕ} (l : Fin M → F) (T : Fin M → Expr F) (hT : ∀ k, (T k).degree ≤ D) :
    (UOV.linComb l T).degree ≤ D :=
  degree_foldl_add (fun k => Expr.const (l k) * T k)
    (fun k => by rw [degree_mul']; simpa [Expr.degree] using hT k) _ _ (by simp [Expr.degree])

theorem degree_qsByte {n D : ℕ} (β : Fin 8 → F) (s : Vector (Expr F) n) (k : ℕ)
    (hk : 8 * k + 8 ≤ n) (hs : ∀ i (hi : i < n), s[i].degree ≤ D) : (qsByte β s k hk).degree ≤ D := by
  have h0 := hs (8 * k) (by omega); have h1 := hs (8 * k + 1) (by omega)
  have h2 := hs (8 * k + 2) (by omega); have h3 := hs (8 * k + 3) (by omega)
  have h4 := hs (8 * k + 4) (by omega); have h5 := hs (8 * k + 5) (by omega)
  have h6 := hs (8 * k + 6) (by omega); have h7 := hs (8 * k + 7) (by omega)
  simp only [qsByte, degree_add', Expr.degree, add_zero]
  omega

theorem degree_bitConstraint_wit (i : ℕ) : (bitConstraint (Expr.wit i : Expr F)).degree = 2 := rfl

/-- A Keccak instance on a `qsInput` has segment constraints of degree `≤ 9` and outputs of
degree `≤ 8`. -/
theorem keccak_deg (pub : Keccak.State) (map : Fin 100 → Option ℕ) (wOff n : ℕ) (hn : n ≤ 800) :
    (∀ e ∈ (qsKeccak wOff n hn (qsInput (F := F) pub map)).1, e.degree ≤ 9) ∧
      ∀ i (hi : i < n), (qsKeccak wOff n hn (qsInput (F := F) pub map)).2[i].degree ≤ 8 :=
  qsKeccak_degree wOff n hn _ fun i hi => qsInput_degree pub map i hi

/-! ## Moussaka -/

section Moussaka

open VoleMole.Arith.Moussaka

theorem bitSystem_deg (B : ℕ) : ∀ e ∈ bitSystem (F := F) B, e.degree ≤ 9 := by
  intro e he
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
  simp [degree_bitConstraint_wit]

/-- Every constraint of Moussaka issue has degree `≤ 9` (`MOUSSAKA_ISSUE_QS_DEGREE`). -/
theorem moussaka_issue_deg (t : Fin M → UInt8) (ctxIss : ℕ → UInt8) :
    ∀ e ∈ issueSystem (F := F) t ctxIss, e.degree ≤ 9 := by
  intro e he
  have hk := keccak_deg (F := F) (issuePub ctxIss) issueMap issueOffStates 360 (by norm_num)
  simp only [issueSystem, List.mem_append] at he
  rcases he with (he | he) | he
  · exact bitSystem_deg _ e he
  · exact hk.1 e he
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
    have := hk.2 i i.isLt
    simp only [issueKeccak, Fin.getElem_fin] at this ⊢
    rw [degree_add']; simp only [Expr.degree]; omega

theorem degree_prefixE : ∀ u, (prefixE (F := F) u).degree ≤ 1
  | 0 => le_rfl
  | u + 1 => by
      have := degree_prefixE u
      simp only [prefixE, degree_add', Expr.degree]; omega

theorem selectorSystem_deg (n : ℕ) : ∀ e ∈ selectorSystem (F := F) n, e.degree ≤ 9 := by
  intro e he
  simp only [selectorSystem, List.mem_append, List.mem_map, List.mem_singleton] at he
  rcases he with (⟨u, -, rfl⟩ | ⟨u, -, rfl⟩) | rfl
  · split_ifs <;> simp [degree_bitConstraint_wit, Expr.degree]
  · have := degree_prefixE (F := F) u
    simp only [Expr.degree]; omega
  · have := degree_prefixE (F := F) 63
    simp only [Expr.degree]; omega

theorem degree_lqExpr (β : Fin 8 → F) (toBits : K → Fin 8 → Bool) (anchors : List (ℕ → K))
    (l : Fin M → F) : (lqExpr β toBits anchors l).degree ≤ 3 := by
  unfold lqExpr
  refine degree_foldl_add _ (fun u => ?_) _ _ (by simp [Expr.degree])
  have := UOV.degree_evalCombinedPublicMap β toBits N M anchors[u]
    (fun i => byteLoad β (redeemOffS + i)) l (fun i => (UOV.degree_byteLoad β _).le)
  rw [degree_mul']; simp only [Expr.degree]; omega

/-- Every constraint of Moussaka redeem has degree `≤ 9` (`MOUSSAKA_REDEEM_QS_DEGREE`); the
output constraint attains it (`lout` has degree 8, `lq` degree 3). -/
theorem moussaka_redeem_deg (β : Fin 8 → F) (toBits : K → Fin 8 → Bool)
    (anchors : List (ℕ → K)) (nf ctxIss ctxRed : ℕ → UInt8) (l : Fin M → F) :
    ∀ e ∈ redeemSystem β toBits anchors nf ctxIss ctxRed l, e.degree ≤ 9 := by
  intro e he
  have hk := keccak_deg (F := F) (redeemPub nf ctxIss ctxRed) redeemMap redeemOffStates 800 le_rfl
  simp only [redeemSystem, List.mem_append, List.mem_singleton] at he
  rcases he with ((he | he) | he) | rfl
  · exact bitSystem_deg _ e he
  · exact selectorSystem_deg _ e he
  · exact hk.1 e he
  · have h1 : (loutExpr β l (redeemKeccak (F := F) nf ctxIss ctxRed).2).degree ≤ 8 :=
      degree_linComb l _ fun k => degree_qsByte β _ _ _ fun i hi => hk.2 i hi
    have h2 := degree_lqExpr β toBits anchors l
    simp only [redeemOutput, degree_add']; omega

end Moussaka

/-! ## Ratatouille -/

section Ratatouille

open VoleMole.Arith.Ratatouille VoleMole.Arith.Adder

theorem bitConstraints_deg (B : ℕ) : ∀ e ∈ bitConstraints (F := F) B, e.degree ≤ 9 := by
  intro e he
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
  simp [degree_bitConstraint_wit]

/-- Every constraint of Ratatouille issue has degree `≤ 9` (`RATATOUILLE_ISSUE_QS_DEGREE`). -/
theorem ratatouille_issue_deg (c : ℕ → UInt8) (tInit : ℕ) (ctx : ℕ → UInt8) :
    ∀ e ∈ issueSystem (F := F) c tInit ctx, e.degree ≤ 9 := by
  intro e he
  have hk := keccak_deg (F := F) (comState zeros ctx tInit zeros) issueComMap 40 256 (by norm_num)
  simp only [issueSystem, List.mem_append] at he
  rcases he with (he | he) | he
  · exact bitConstraints_deg _ e he
  · exact hk.1 e he
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
    have := hk.2 i i.isLt
    simp only [issueKeccak, Fin.getElem_fin] at this ⊢
    rw [degree_add']; simp only [Expr.degree]; omega

theorem degree_carry (off i : ℕ) : (carry (F := F) off i).degree ≤ 1 := by
  unfold carry; split_ifs <;> simp [Expr.degree]

theorem addCredits_deg (a b : ℕ → Expr F) (off : ℕ) (ha : ∀ i, (a i).degree ≤ 1)
    (hb : ∀ i, (b i).degree ≤ 1) :
    (∀ e ∈ (addCredits a b off).1, e.degree ≤ 2) ∧
      ∀ i (hi : i < 65), (addCredits a b off).2[i].degree ≤ 1 := by
  refine ⟨fun e he => ?_, fun i hi => ?_⟩
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
    have := ha i; have := hb i; have := degree_carry (F := F) off i
    simp only [Expr.degree]; omega
  · simp only [addCredits, Vector.getElem_ofFn]
    split_ifs
    · have := ha i; have := hb i; have := degree_carry (F := F) off i
      simp only [degree_add']; omega
    · exact degree_carry off 64

theorem creditWit_deg (o i : ℕ) : (creditWit (F := F) o i).degree ≤ 1 := le_rfl
theorem dBits_deg (d i : ℕ) : (dBits (F := F) d i).degree ≤ 1 := by simp [dBits, Expr.degree]

/-- Every constraint of Ratatouille spend has degree `≤ 9` (`RATATOUILLE_SPEND_QS_DEGREE`). -/
theorem ratatouille_spend_deg (β : Fin 8 → F) (toBits : K → Fin 8 → Bool) (pk : ℕ → K)
    (nf : ℕ → UInt8) (d : ℕ) (cNext ctx : ℕ → UInt8) (l : Fin uovM → F) :
    ∀ e ∈ spendSystem β toBits pk nf d cNext ctx l, e.degree ≤ 9 := by
  intro e he
  have s1 := addCredits_deg (F := F) (creditWit 16) (creditWit 24) 231 (creditWit_deg _)
    (creditWit_deg _)
  have s2 := addCredits_deg (F := F) (creditWit 88) (dBits d) 239 (creditWit_deg _) (dBits_deg d)
  have kc := keccak_deg (F := F) (comState nf ctx 0 zeros) spendComMap 247 256 (by norm_num)
  have kt := keccak_deg (F := F) (tagState zeros 0) spendTagMap 447 360 (by norm_num)
  have kn := keccak_deg (F := F) (comState zeros ctx 0 zeros) spendComNextMap 647 256 (by norm_num)
  simp only [spendSystem, List.mem_append, List.mem_singleton] at he
  rcases he with (((((((((he | he) | he) | he) | he) | he) | he) | rfl) | he) | he)
  · exact bitConstraints_deg _ e he
  · exact (s1.1 e he).trans (by norm_num)
  · exact (s2.1 e he).trans (by norm_num)
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
    have h1 := s1.2 i i.isLt; have h2 := s2.2 i i.isLt
    simp only [spendSum1, spendSum2, Fin.getElem_fin] at h1 h2 ⊢
    rw [degree_add']; omega
  · exact kc.1 e he
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
    have := kc.2 i i.isLt
    simp only [spendCom, Fin.getElem_fin] at this ⊢
    rw [degree_add']; simp only [Expr.degree]; omega
  · exact kt.1 e he
  · have h1 : (tagCombination β l (spendTag (F := F)).2).degree ≤ 8 :=
      degree_linComb l _ fun k => degree_qsByte β _ _ _ fun i hi => kt.2 i hi
    have h2 := UOV.degree_evalCombinedPublicMap β toBits uovN uovM pk
      (fun i => byteLoad β (112 + i)) l (fun i => (UOV.degree_byteLoad β _).le)
    simp only [combinedConstraint, degree_add']; omega
  · exact kn.1 e he
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 he
    have := kn.2 i i.isLt
    simp only [spendComNext, Fin.getElem_fin] at this ⊢
    rw [degree_add']; simp only [Expr.degree]; omega

end Ratatouille

end VoleMole.EndToEnd.Degree
