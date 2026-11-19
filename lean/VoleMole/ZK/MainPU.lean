import VoleMole.ZK.MainGame
import VoleMole.Privacy.PU

/-!
# The (PU) event of `main_chain_le` on simulated proofs: candidate sets, and a uniform `d`

`main_chain_le` (`ZK/MainGame.lean`) leaves the term `Pr[predAll]`: in the game with all four
proofs simulated, some proof's witness prefix is a candidate of its `H₅` read set (`predJ`). The
protocol files (`Privacy/MoussakaMainPU.lean`, `Privacy/RatatouilleMainPU.lean`) turn it into the
advantage of explicit predictors in the game `Privacy.PU.puAdv`. Here are the two generic steps.

* **`candJ`**: for a simulated proof with coins `k`, a statement `st` and a set `S5` of `H₅` keys,
  the set of 16-byte values `r` that are candidates for the witness prefix. `predJ_simP`: on the
  simulator slot, `predJ` says that the witness prefix is in `candJ`; `card_candJ_le`: at most
  `|S5| + 1` candidates. `candJ` reads the simulator's shared tape, corrections and `d`, the
  statement and `S5`: nothing of the witness.
* **`pr_thetaMain_le`, `pr_d3_le`, `pr_d4_le`**: if neither the target nor the candidates for the
  label offset depend on the simulator's uniform field `d` (as when the simulated proof is not
  shown to the adversary), then `thetaMain d[0..16) target` is a candidate with probability at
  most `(q + 1)·2⁻¹²⁸`, whatever the target. This covers the proofs of a game that are computed but
  not revealed.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.Privacy

/-- **`pr` does not depend on the `Fintype` instance** (the game tapes of `MainChain.ev` carry the
slots' instances; the reductions use the instances of the product types). -/
theorem pr_inst_irrel {α : Type*} (i₁ i₂ : Fintype α) (P : α → Prop) :
    @pr α i₁ P = @pr α i₂ P := by
  rw [Subsingleton.elim i₁ i₂]

end VoleMole.Privacy

namespace VoleMole.ZK.Sim

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy
open VoleMole.Privacy.MainChain

attribute [local instance] decEqW128
attribute [local irreducible] simulate proveIdeal proveE firstHit

variable [HasPrg]

/-! ## The candidate set of a simulated proof -/

section Cand

variable (Hb : Hashes) (T : CrtTables) {p : Params}

/-- **The candidates for the witness prefix of a simulated proof**: with the simulator's coins `k`
(its shared tape, corrections and `d`), the statement `st` and the `H₅` keys `S5`, the 16-byte
values `r` such that `thetaMain d[0..16) r` is a candidate for the label offset. -/
noncomputable def candJ (hm : MainP p) (st : Statement) (S5 : Finset (SKey p)) (k : SimCoins p) :
    Finset (Bytes 16) :=
  univ.filter fun r => thetaMain (pre16 hm.hw k.2.2.2.2.1) r ∈
    guessSet Hb T (withP st p) S5 k.1 (fieldsCD k.2.1 k.2.2.2.2.1)

lemma mem_candJ (hm : MainP p) {st : Statement} {S5 : Finset (SKey p)} {k : SimCoins p}
    {r : Bytes 16} : r ∈ candJ Hb T hm st S5 k ↔ thetaMain (pre16 hm.hw k.2.2.2.2.1) r ∈
      guessSet Hb T (withP st p) S5 k.1 (fieldsCD k.2.1 k.2.2.2.2.1) := by
  unfold candJ
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

/-- **At most `|S5| + 1` candidates.** -/
lemma card_candJ_le (hm : MainP p) (st : Statement) (S5 : Finset (SKey p)) (k : SimCoins p) :
    (candJ Hb T hm st S5 k).card ≤ S5.card + 1 := by
  refine le_trans ?_ (card_guessSet_le Hb T (withP st p) S5 k.1 (fieldsCD k.2.1 k.2.2.2.2.1))
  refine Finset.card_le_card_of_injOn (thetaMain (pre16 hm.hw k.2.2.2.2.1)) (fun r hr => ?_)
    (fun r _ r' _ h => thetaMain_injective _ h)
  rw [mem_coe, mem_candJ] at hr
  exact hr

/-- **On the simulator slot, `predJ` is membership in `candJ`.** -/
lemma predJ_simP (hm : MainP p) (S5 : Finset (SKey p)) (y : SW) (k : SimCoins p × Vis p) :
    predJ Hb T hm S5 ((simP p).obs (some y) k) ↔ wPre y.2 ∈ candJ Hb T hm y.1 S5 k.1 := by
  rw [mem_candJ]
  exact Iff.rfl

lemma predJ_simP_none (hm : MainP p) (S5 : Finset (SKey p)) (k : SimCoins p × Vis p) :
    ¬ predJ Hb T hm S5 ((simP p).obs none k) := id

/-- The candidates for the label offset do not depend on `d`. -/
lemma guessSet_fieldsCD (st : Statement) (S5 : Finset (SKey p)) (s : Shared)
    (c : Bytes (16 * p.correctionBytes)) (d d' : Bytes p.witnessBytes) :
    guessSet Hb T (withP st p) S5 s (fieldsCD c d) = guessSet Hb T (withP st p) S5 s (fieldsCD c d') :=
  guessSet_congr_fst T Hb (withP st p) S5 s rfl

end Cand

/-! ## A uniform `d` -/

section UniformD

lemma thetaMain_injective_left (r : Bytes 16) : Function.Injective fun d => thetaMain d r := by
  intro d d' h
  have h1 := w16_injective h
  funext k
  have := congrFun h1 k
  simp only [xor16] at this
  exact (UInt8.xor_left_inj _).1 this

/-- The first 16 bytes of a uniform block are uniform. -/
lemma pr_pre16 {m : ℕ} (P : Bytes 16 → Prop) :
    pr (Bytes (16 + m)) (fun d => P (pre16 (Nat.le_add_right 16 m) d)) = pr (Bytes 16) P := by
  rw [← pr_equiv (Fin.appendEquiv 16 m), ← pr_prod_fst (β := Bytes m) P]
  refine pr_congr fun z => ?_
  have : pre16 (Nat.le_add_right 16 m) (Fin.appendEquiv 16 m z) = z.1 := by
    funext k
    exact Fin.append_left z.1 z.2 k
  rw [this]

/-- **A uniform `d` hits a fixed candidate set with probability `≤ (q + 1)·2⁻¹²⁸`**, whatever the
target `ρ`: `thetaMain d[0..16) ρ ∈ G` for a set `G` of at most `q + 1` label offsets, with `ρ`
and `G` functions of coins independent of `d`. -/
theorem pr_thetaMain_le {n : ℕ} (hn : 16 ≤ n) {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (ρ : Ω → Bytes 16) (G : Ω → Finset W128) {q : ℕ} (hG : ∀ ω, (G ω).card ≤ q + 1) :
    pr (Bytes n × Ω) (fun z => thetaMain (pre16 hn z.1) (ρ z.2) ∈ G z.2) ≤ (q + 1) / 2 ^ 128 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [← pr_equiv (Equiv.prodComm Ω (Bytes (16 + m)))]
  refine pr_prod_le _ fun ω => ?_
  show pr (Bytes (16 + m)) (fun d => thetaMain (pre16 (Nat.le_add_right 16 m) d) (ρ ω) ∈ G ω) ≤ _
  rw [pr_pre16 (fun u => thetaMain u (ρ ω) ∈ G ω)]
  refine (pr_mem_le (fun u => thetaMain u (ρ ω)) (thetaMain_injective_left (ρ ω)) (G ω)).trans ?_
  rw [Prob.card_bytes]
  have : ((G ω).card : ℝ) ≤ q + 1 := by exact_mod_cast hG ω
  have h2 : ((2 ^ (8 * 16) : ℕ) : ℝ) = 2 ^ 128 := by norm_num
  rw [h2]
  gcongr

variable {S K₁ K₂ K₃ K₄ Sh C X Y Z V : Type} [Fintype S] [Nonempty S] [Fintype K₁] [Nonempty K₁]
  [Fintype K₂] [Nonempty K₂] [Fintype K₃] [Nonempty K₃] [Fintype K₄] [Nonempty K₄] [Fintype Sh]
  [Nonempty Sh] [Fintype C] [Nonempty C] [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
  [Fintype Z] [Nonempty Z] [Fintype V] [Nonempty V]

/-- **The third slot's `d`**, in a tape `(s, k₁, k₂, k₃, k₄)` with `k₃ = ((shared, (c, x, y, d,
z)), tables)`: if the target and the candidates are functions of the tape without `d`, the bound of
`pr_thetaMain_le` holds. -/
theorem pr_d3_le {n : ℕ} (hn : 16 ≤ n) (ρ : S × K₁ × K₂ × ((Sh × (C × X × Y × Z)) × V) × K₄ → Bytes 16)
    (G : S × K₁ × K₂ × ((Sh × (C × X × Y × Z)) × V) × K₄ → Finset W128) {q : ℕ}
    (hG : ∀ ω, (G ω).card ≤ q + 1) :
    pr (S × K₁ × K₂ × ((Sh × (C × X × Y × Bytes n × Z)) × V) × K₄) (fun x =>
      thetaMain (pre16 hn x.2.2.2.1.1.2.2.2.2.1)
        (ρ (x.1, x.2.1, x.2.2.1, ((x.2.2.2.1.1.1, (x.2.2.2.1.1.2.1, x.2.2.2.1.1.2.2.1,
          x.2.2.2.1.1.2.2.2.1, x.2.2.2.1.1.2.2.2.2.2)), x.2.2.2.1.2), x.2.2.2.2)) ∈
        G (x.1, x.2.1, x.2.2.1, ((x.2.2.2.1.1.1, (x.2.2.2.1.1.2.1, x.2.2.2.1.1.2.2.1,
          x.2.2.2.1.1.2.2.2.1, x.2.2.2.1.1.2.2.2.2.2)), x.2.2.2.1.2), x.2.2.2.2)) ≤
      (q + 1) / 2 ^ 128 := by
  let e : Bytes n × (S × K₁ × K₂ × ((Sh × (C × X × Y × Z)) × V) × K₄) ≃
      S × K₁ × K₂ × ((Sh × (C × X × Y × Bytes n × Z)) × V) × K₄ :=
    { toFun := fun z => (z.2.1, z.2.2.1, z.2.2.2.1, ((z.2.2.2.2.1.1.1, (z.2.2.2.2.1.1.2.1,
        z.2.2.2.2.1.1.2.2.1, z.2.2.2.2.1.1.2.2.2.1, z.1, z.2.2.2.2.1.1.2.2.2.2)), z.2.2.2.2.1.2),
        z.2.2.2.2.2)
      invFun := fun x => (x.2.2.2.1.1.2.2.2.2.1, (x.1, x.2.1, x.2.2.1, ((x.2.2.2.1.1.1,
        (x.2.2.2.1.1.2.1, x.2.2.2.1.1.2.2.1, x.2.2.2.1.1.2.2.2.1, x.2.2.2.1.1.2.2.2.2.2)),
        x.2.2.2.1.2), x.2.2.2.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e]
  exact pr_thetaMain_le hn ρ G hG

/-- **The fourth slot's `d`** (as `pr_d3_le`). -/
theorem pr_d4_le {n : ℕ} (hn : 16 ≤ n) (ρ : S × K₁ × K₂ × K₃ × ((Sh × (C × X × Y × Z)) × V) → Bytes 16)
    (G : S × K₁ × K₂ × K₃ × ((Sh × (C × X × Y × Z)) × V) → Finset W128) {q : ℕ}
    (hG : ∀ ω, (G ω).card ≤ q + 1) :
    pr (S × K₁ × K₂ × K₃ × ((Sh × (C × X × Y × Bytes n × Z)) × V)) (fun x =>
      thetaMain (pre16 hn x.2.2.2.2.1.2.2.2.2.1)
        (ρ (x.1, x.2.1, x.2.2.1, x.2.2.2.1, ((x.2.2.2.2.1.1, (x.2.2.2.2.1.2.1, x.2.2.2.2.1.2.2.1,
          x.2.2.2.2.1.2.2.2.1, x.2.2.2.2.1.2.2.2.2.2)), x.2.2.2.2.2))) ∈
        G (x.1, x.2.1, x.2.2.1, x.2.2.2.1, ((x.2.2.2.2.1.1, (x.2.2.2.2.1.2.1, x.2.2.2.2.1.2.2.1,
          x.2.2.2.2.1.2.2.2.1, x.2.2.2.2.1.2.2.2.2.2)), x.2.2.2.2.2))) ≤
      (q + 1) / 2 ^ 128 := by
  let e : Bytes n × (S × K₁ × K₂ × K₃ × ((Sh × (C × X × Y × Z)) × V)) ≃
      S × K₁ × K₂ × K₃ × ((Sh × (C × X × Y × Bytes n × Z)) × V) :=
    { toFun := fun z => (z.2.1, z.2.2.1, z.2.2.2.1, z.2.2.2.2.1, ((z.2.2.2.2.2.1.1,
        (z.2.2.2.2.2.1.2.1, z.2.2.2.2.2.1.2.2.1, z.2.2.2.2.2.1.2.2.2.1, z.1,
        z.2.2.2.2.2.1.2.2.2.2)), z.2.2.2.2.2.2))
      invFun := fun x => (x.2.2.2.2.1.2.2.2.2.1, (x.1, x.2.1, x.2.2.1, x.2.2.2.1, ((x.2.2.2.2.1.1,
        (x.2.2.2.2.1.2.1, x.2.2.2.2.1.2.2.1, x.2.2.2.2.1.2.2.2.1, x.2.2.2.2.1.2.2.2.2.2)),
        x.2.2.2.2.2)))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e]
  exact pr_thetaMain_le hn ρ G hG

end UniformD

end VoleMole.ZK.Sim
