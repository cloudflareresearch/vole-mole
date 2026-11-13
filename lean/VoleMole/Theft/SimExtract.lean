import VoleMole.Theft.Reads

/-!
# Weak simulation-extractability from plain extraction: the programming step of L8

`WeakSE2` (`Theft/Basic.lean`) is weak simulation-extractability for two simulated proofs whose
simulators **program** the shared tables. L8 (`docs/extraction/L8-simulation-extractability.md`)
proves it on paper by showing that the programming does not help: the simulator programs `H₂³`
only at the grinding points of its own proofs' prefixes (S1), and an accepting forgery with a fresh
statement must avoid those points. Here that step is mechanized, in the table model of the
zero-knowledge theorems, for any simulators whose programming changes only one part of the tables:

* **`PlainSE`**: extraction **without simulated proofs and without programming**. The adversary has
  advice `a` (of any finite type), public "honest" statement–proof pairs `p₁ a`, `p₂ a` (any values
  independent of the tables; they only define freshness) and a last stage `F a g₁ g₂ s` on uniform
  tables. It wins if its output is accepted, fresh, and the extractor's witness is not one. The
  extractor `e` sees the pairs, the output, the slices and the part `s.2` of the tables that the
  simulators do not program (for the Lean simulators: `H₅` and the cipher, not `H₂³`).
* **`ProgMoves`**: the event that the adversary's fresh output is accepted on the programmed tables
  but not on the unprogrammed ones: the programming moved the verifier's answer. For the Lean
  verifiers this happens only when the verifier's single `H₂³` query (`chal3`'s input) is a point
  the simulators programmed (`verRO_prog_eq`, `progRO_moved`, `accOp_moves`): the forgery's grinding
  prefix `chal2 ‖ qs_check ‖ ã` is one of the simulated proofs' prefixes.
* **`weakSE2_of_plain`**: if the programming leaves `s.2` unchanged, the extractor reads only `s.2`
  (`extOf e`), and the adversary's last stage composed with the programming is admissible for
  `PlainSE`, then

      WeakSE2 ≤ ε_plain + ε_moves.

  The reduction runs the simulators itself (their coins are part of its advice) and answers the
  programmed points from them; the extractor's view is the same in both worlds because it does not
  read the programmed part.
* **`noTheft_lean_plain`**, **`noRedirect_lean_plain`**: the theft theorems with the Lean prover,
  verifiers and simulators, the hops' budgets proved (`Theft/Reads.lean`), and `WeakSE2` replaced by
  `PlainSE` (budget of the adversary composed with both programmings: `H₅` `+624`, cipher `+9214`)
  and `ProgMoves`.

**What remains.** `PlainSE` and `ProgMoves` are hypotheses. In this table model the hashes other
than `H₂³`, `H₅`, `H₃` and the cipher (`H₂⁰`, `H₂¹`, `H₂²`, `H₄`, `H₁`) are SHAKE, fixed functions,
and an adversary is any function of the tables: only its table reads are bounded, not its
computation. Plain extraction rests on `chal1` and `chal2` being random (L3, L4) and `ProgMoves`
on collision resistance of the chain (`chal2` determines the statement), neither of which holds
for a fixed function against unbounded adversaries. They are proved in the random-oracle model of
`ROM/` (`*_accept_le_adaptive`, `omuf_le_num_sim`, `balance_le_sim_num`), where every hash is a
random oracle and adversaries make bounded queries; carrying those bounds into this model needs
`H₂⁰`–`H₂²` as random tables here (or the simulators in `ROM/`), which is not done.
-/

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

open Finset

namespace VoleMole.Theft

open VoleMole.Privacy

/-! ## Plain extraction and the programming step -/

section Generic

variable {I₁ I₂ P₁ P₂ G A B Out W : Type*} {C₁ C₂ : Type}

/-- The tables both simulations programmed, in the order of `real_sim_le`. -/
def progT (prog₁ : I₁ → C₁ → A × B → A × B) (prog₂ : I₂ → C₂ → A × B → A × B)
    (x₁ : Option I₁) (c₁ : C₁) (x₂ : Option I₂) (c₂ : C₂) (s : A × B) : A × B :=
  progO prog₁ x₁ c₁ (progO prog₂ x₂ c₂ s)

lemma progO_snd {I C : Type*} {prog : I → C → A × B → A × B} (hp : ∀ x c s, (prog x c s).2 = s.2)
    (x : Option I) (c : C) (s : A × B) : (progO prog x c s).2 = s.2 := by
  rcases x with _ | x
  · rfl
  · exact hp x c s

lemma progT_snd {prog₁ : I₁ → C₁ → A × B → A × B} {prog₂ : I₂ → C₂ → A × B → A × B}
    (hp₁ : ∀ x c s, (prog₁ x c s).2 = s.2) (hp₂ : ∀ x c s, (prog₂ x c s).2 = s.2)
    (x₁ : Option I₁) (c₁ : C₁) (x₂ : Option I₂) (c₂ : C₂) (s : A × B) :
    (progT prog₁ prog₂ x₁ c₁ x₂ c₂ s).2 = s.2 := by
  unfold progT
  rw [progO_snd hp₁, progO_snd hp₂]

/-- **An extractor that does not read the programmed part** of the tables: it sees the honest
pairs, the adversary's output, the slices and `s.2`. -/
def extOf (e : Option (I₁ × P₁) → Option (I₂ × P₂) → Out → G → G → B → W) :
    Option (I₁ × P₁) → Option (I₂ × P₂) → (G → G → A × B → Out) → G → G → A × B → W :=
  fun p₁ p₂ F g₁ g₂ s => e p₁ p₂ (F g₁ g₂ s) g₁ g₂ s.2

variable [Fintype G] [Fintype A] [Fintype B]

/-- **Plain extraction** (no simulated proofs, no programming), with error `ε`, against the
adversaries `Adm` admits. The adversary has advice `a`, honest pairs `p₁ a`, `p₂ a` that define
freshness (any values, not read off the tables) and a last stage `F a` on uniform slices and
tables. The extractor `e` sees the pairs, the output, the slices and `s.2`. -/
def PlainSE (Acc : Out → A × B → Prop) (Fresh : Option (I₁ × P₁) → Option (I₂ × P₂) → Out → Prop)
    (Rel : Out → W → Prop) (e : Option (I₁ × P₁) → Option (I₂ × P₂) → Out → G → G → B → W)
    (Adm : (G → G → A × B → Out) → Prop) (ε : ℝ) : Prop :=
  ∀ (α : Type) [Fintype α] [Nonempty α] (p₁ : α → Option (I₁ × P₁)) (p₂ : α → Option (I₂ × P₂))
    (F : α → G → G → A × B → Out), (∀ a, Adm (F a)) →
    pr (α × ((G × G) × (A × B))) (fun z =>
      Acc (F z.1 z.2.1.1 z.2.1.2 z.2.2) z.2.2 ∧ Fresh (p₁ z.1) (p₂ z.1) (F z.1 z.2.1.1 z.2.1.2 z.2.2) ∧
        ¬ Rel (F z.1 z.2.1.1 z.2.1.2 z.2.2)
          (e (p₁ z.1) (p₂ z.1) (F z.1 z.2.1.1 z.2.1.2 z.2.2) z.2.1.1 z.2.1.2 z.2.2.2)) ≤ ε

variable [Fintype C₁] [Fintype C₂]

/-- **The programming moves the verifier**, with probability at most `ε`: in `WeakSE2`'s game, the
adversary's output is fresh, accepted on the programmed tables and rejected on the unprogrammed
ones. -/
def ProgMoves (sim₁ : I₁ → C₁ → Option P₁) (prog₁ : I₁ → C₁ → A × B → A × B)
    (sim₂ : I₂ → C₂ → Option P₂) (prog₂ : I₂ → C₂ → A × B → A × B) (Acc : Out → A × B → Prop)
    (Fresh : Option (I₁ × P₁) → Option (I₂ × P₂) → Out → Prop)
    (Adm : (G → G → A × B → Out) → Prop) (ε : ℝ) : Prop :=
  ∀ (α : Type) [Fintype α] [Nonempty α] (x₁ : α → Option I₁) (x₂ : α → Option P₁ → Option I₂)
    (out : α → Option P₁ → Option P₂ → G → G → A × B → Out),
    (∀ a π₁ π₂, Adm (out a π₁ π₂)) →
    pr ((α × (C₁ × G)) × ((C₂ × G) × (A × B))) (fun z =>
      Fresh (pairO (x₁ z.1.1) (simO sim₁ (x₁ z.1.1) z.1.2.1))
          (pairO (x₂ z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1))
            (simO sim₂ (x₂ z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)) z.2.1.1))
          (out z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)
            (simO sim₂ (x₂ z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)) z.2.1.1) z.1.2.2 z.2.1.2
            (progT prog₁ prog₂ (x₁ z.1.1) z.1.2.1 (x₂ z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)) z.2.1.1
              z.2.2)) ∧
        Acc (out z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)
            (simO sim₂ (x₂ z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)) z.2.1.1) z.1.2.2 z.2.1.2
            (progT prog₁ prog₂ (x₁ z.1.1) z.1.2.1 (x₂ z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)) z.2.1.1
              z.2.2))
          (progT prog₁ prog₂ (x₁ z.1.1) z.1.2.1 (x₂ z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)) z.2.1.1
            z.2.2) ∧
        ¬ Acc (out z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)
            (simO sim₂ (x₂ z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)) z.2.1.1) z.1.2.2 z.2.1.2
            (progT prog₁ prog₂ (x₁ z.1.1) z.1.2.1 (x₂ z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)) z.2.1.1
              z.2.2)) z.2.2) ≤ ε

/-- **An event of the programming**, with probability at most `ε`: in `WeakSE2`'s game, the
adversary's output `o` is fresh and `E o s' s` holds for the programmed tables `s'` and the
unprogrammed ones `s`. (`ProgMoves` is the event "`o` is accepted on `s'` and not on `s`"; for the
Lean verifiers it implies `HitPt`, `accOp_moves`.) -/
def ProgEv (sim₁ : I₁ → C₁ → Option P₁) (prog₁ : I₁ → C₁ → A × B → A × B)
    (sim₂ : I₂ → C₂ → Option P₂) (prog₂ : I₂ → C₂ → A × B → A × B)
    (Fresh : Option (I₁ × P₁) → Option (I₂ × P₂) → Out → Prop) (E : Out → A × B → A × B → Prop)
    (Adm : (G → G → A × B → Out) → Prop) (ε : ℝ) : Prop :=
  ∀ (α : Type) [Fintype α] [Nonempty α] (x₁ : α → Option I₁) (x₂ : α → Option P₁ → Option I₂)
    (out : α → Option P₁ → Option P₂ → G → G → A × B → Out),
    (∀ a π₁ π₂, Adm (out a π₁ π₂)) →
    pr ((α × (C₁ × G)) × ((C₂ × G) × (A × B))) (fun z =>
      Fresh (pairO (x₁ z.1.1) (simO sim₁ (x₁ z.1.1) z.1.2.1))
          (pairO (x₂ z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1))
            (simO sim₂ (x₂ z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)) z.2.1.1))
          (out z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)
            (simO sim₂ (x₂ z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)) z.2.1.1) z.1.2.2 z.2.1.2
            (progT prog₁ prog₂ (x₁ z.1.1) z.1.2.1 (x₂ z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)) z.2.1.1
              z.2.2)) ∧
        E (out z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)
            (simO sim₂ (x₂ z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)) z.2.1.1) z.1.2.2 z.2.1.2
            (progT prog₁ prog₂ (x₁ z.1.1) z.1.2.1 (x₂ z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)) z.2.1.1
              z.2.2))
          (progT prog₁ prog₂ (x₁ z.1.1) z.1.2.1 (x₂ z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)) z.2.1.1
            z.2.2) z.2.2) ≤ ε

/-- **`ProgMoves` from a larger event**: if every output accepted on the programmed tables and
rejected on the unprogrammed ones satisfies `E` (for tables that agree on `s.2`), the
programming moves the verifier at most as often as `E` holds. -/
theorem progMoves_of_ev {sim₁ : I₁ → C₁ → Option P₁} {prog₁ : I₁ → C₁ → A × B → A × B}
    {sim₂ : I₂ → C₂ → Option P₂} {prog₂ : I₂ → C₂ → A × B → A × B} {Acc : Out → A × B → Prop}
    {Fresh : Option (I₁ × P₁) → Option (I₂ × P₂) → Out → Prop} {E : Out → A × B → A × B → Prop}
    {Adm : (G → G → A × B → Out) → Prop} {ε : ℝ}
    (hp₁ : ∀ x c s, (prog₁ x c s).2 = s.2) (hp₂ : ∀ x c s, (prog₂ x c s).2 = s.2)
    (hE : ∀ o s' s, s'.2 = s.2 → Acc o s' → ¬ Acc o s → E o s' s)
    (h : ProgEv sim₁ prog₁ sim₂ prog₂ Fresh E Adm ε) :
    ProgMoves sim₁ prog₁ sim₂ prog₂ Acc Fresh Adm ε := by
  intro α _ _ x₁ x₂ out hout
  refine (pr_mono fun z hz => ⟨hz.1, hE _ _ _ (progT_snd hp₁ hp₂ _ _ _ _ _) hz.2.1 hz.2.2⟩).trans
    (h α x₁ x₂ out hout)

/-- **Non-vacuity**: both notions hold with error `1`. -/
theorem plainSE_one (Acc : Out → A × B → Prop)
    (Fresh : Option (I₁ × P₁) → Option (I₂ × P₂) → Out → Prop) (Rel : Out → W → Prop)
    (e : Option (I₁ × P₁) → Option (I₂ × P₂) → Out → G → G → B → W)
    (Adm : (G → G → A × B → Out) → Prop) : PlainSE Acc Fresh Rel e Adm 1 :=
  fun _ _ _ _ _ _ _ => pr_le_one _

theorem progMoves_one (sim₁ : I₁ → C₁ → Option P₁) (prog₁ : I₁ → C₁ → A × B → A × B)
    (sim₂ : I₂ → C₂ → Option P₂) (prog₂ : I₂ → C₂ → A × B → A × B) (Acc : Out → A × B → Prop)
    (Fresh : Option (I₁ × P₁) → Option (I₂ × P₂) → Out → Prop)
    (Adm : (G → G → A × B → Out) → Prop) : ProgMoves sim₁ prog₁ sim₂ prog₂ Acc Fresh Adm 1 :=
  fun _ _ _ _ _ _ _ => pr_le_one _

theorem progEv_one (sim₁ : I₁ → C₁ → Option P₁) (prog₁ : I₁ → C₁ → A × B → A × B)
    (sim₂ : I₂ → C₂ → Option P₂) (prog₂ : I₂ → C₂ → A × B → A × B)
    (Fresh : Option (I₁ × P₁) → Option (I₂ × P₂) → Out → Prop) (E : Out → A × B → A × B → Prop)
    (Adm : (G → G → A × B → Out) → Prop) : ProgEv sim₁ prog₁ sim₂ prog₂ Fresh E Adm 1 :=
  fun _ _ _ _ _ _ _ => pr_le_one _

/-- The reduction's tape: the advice is the adversary's coins and both simulators' coins. -/
def seEquiv (α : Type*) : (α × (C₁ × G)) × ((C₂ × G) × (A × B)) ≃
    (α × C₁ × C₂) × ((G × G) × (A × B)) where
  toFun z := ((z.1.1, z.1.2.1, z.2.1.1), ((z.1.2.2, z.2.1.2), z.2.2))
  invFun z := ((z.1.1, (z.1.2.1, z.2.1.1)), ((z.1.2.2, z.2.1.2), z.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Weak simulation-extractability from plain extraction.** If the simulators' programming
leaves `s.2` unchanged and the adversary's last stage composed with any programming is admissible
for plain extraction, the extractor `extOf e` (which reads only `s.2`) is weakly
simulation-extractable with error `ε_plain + ε_moves`. -/
theorem weakSE2_of_plain [Nonempty C₁] [Nonempty C₂] {sim₁ : I₁ → C₁ → Option P₁} {prog₁ : I₁ → C₁ → A × B → A × B}
    {sim₂ : I₂ → C₂ → Option P₂} {prog₂ : I₂ → C₂ → A × B → A × B} {Acc : Out → A × B → Prop}
    {Fresh : Option (I₁ × P₁) → Option (I₂ × P₂) → Out → Prop} {Rel : Out → W → Prop}
    {e : Option (I₁ × P₁) → Option (I₂ × P₂) → Out → G → G → B → W}
    {Adm Adm₀ : (G → G → A × B → Out) → Prop} {ε₀ εm : ℝ}
    (hplain : PlainSE Acc Fresh Rel e Adm₀ ε₀)
    (hmoves : ProgMoves sim₁ prog₁ sim₂ prog₂ Acc Fresh Adm εm)
    (hp₁ : ∀ x c s, (prog₁ x c s).2 = s.2) (hp₂ : ∀ x c s, (prog₂ x c s).2 = s.2)
    (hadm : ∀ F x₁ c₁ x₂ c₂, Adm F →
      Adm₀ (fun g₁ g₂ s => F g₁ g₂ (progT prog₁ prog₂ x₁ c₁ x₂ c₂ s))) :
    WeakSE2 sim₁ prog₁ sim₂ prog₂ Acc Fresh Rel (extOf e) Adm (ε₀ + εm) := by
  intro α _ _ x₁ x₂ out hout
  have hP := hplain (α × C₁ × C₂) (fun b => pairO (x₁ b.1) (simO sim₁ (x₁ b.1) b.2.1))
    (fun b => pairO (x₂ b.1 (simO sim₁ (x₁ b.1) b.2.1))
      (simO sim₂ (x₂ b.1 (simO sim₁ (x₁ b.1) b.2.1)) b.2.2))
    (fun b g₁ g₂ s => out b.1 (simO sim₁ (x₁ b.1) b.2.1)
      (simO sim₂ (x₂ b.1 (simO sim₁ (x₁ b.1) b.2.1)) b.2.2) g₁ g₂
      (progT prog₁ prog₂ (x₁ b.1) b.2.1 (x₂ b.1 (simO sim₁ (x₁ b.1) b.2.1)) b.2.2 s))
    fun b => hadm _ _ _ _ _ (hout _ _ _)
  rw [← pr_equiv (seEquiv α)] at hP
  have hM := hmoves α x₁ x₂ out hout
  refine (pr_mono fun z hz => ?_).trans ((pr_or_le _ _).trans (add_le_add hP hM))
  obtain ⟨hacc, hfr, hrel⟩ := hz
  by_cases h : Acc (out z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)
      (simO sim₂ (x₂ z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)) z.2.1.1) z.1.2.2 z.2.1.2
      (progT prog₁ prog₂ (x₁ z.1.1) z.1.2.1 (x₂ z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1)) z.2.1.1
        z.2.2)) z.2.2
  · left
    refine ⟨h, hfr, ?_⟩
    have e2 := progT_snd hp₁ hp₂ (x₁ z.1.1) z.1.2.1 (x₂ z.1.1 (simO sim₁ (x₁ z.1.1) z.1.2.1))
      z.2.1.1 z.2.2
    simp only [extOf] at hrel
    unfold progT at e2 ⊢
    rw [e2] at hrel
    exact hrel
  · right
    exact ⟨hfr, hacc, h⟩

end Generic

/-! ## The Lean verifier reads `H₂³` at one point, and the Lean simulator programs its prefix -/

section Lean

open VoleMole.ZK.Sim VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK

variable {R : Type} [CipherRow R] {p : Params}

/-- **The verifier's single `H₂³` input** on the tables `s`: `chal3`'s input
`vPre ‖ ctr ‖ 11` (the recomputed prefix `chal2 ‖ qs_check ‖ ã` does not read `H₂³`). -/
noncomputable def vPoint (Hb : Hashes) (st : Statement) (proof : ByteArray) (s : ShG R p) :
    ByteArray :=
  (@vPre (icPrg (rowFn s.2.2)) (recV p Hb s.1 s.2.1) CrtGen.tables st proof ++
    (⟨st.params, proof⟩ : Proof).ctr).push 11

/-- **The verifier on two `H₂³` tables** that agree at the keys of its `H₂³` input (and tables
that agree elsewhere) gives the same transcript. -/
theorem verRO_h23_eq (Hb : Hashes) (st : Statement) (proof : ByteArray) (s s' : ShG R p)
    (h2 : s'.2 = s.2) (hk : ∀ k, enc2 p k = vPoint Hb st proof s → s'.1 k = s.1 k) :
    verRO p Hb st proof s' = verRO p Hb st proof s := by
  obtain ⟨G2', rest'⟩ := s'
  obtain ⟨G2, G5, E⟩ := s
  simp only at h2
  subst h2
  unfold verRO
  have hA : (recV p Hb G2' G5).AgreeOff .h23 (recV p Hb G2 G5) := by
    intro k hk
    funext x
    by_cases h5 : k = .h5
    · subst h5; simp only [recV, Hashes.withTable, reduceCtorEq, ite_true, ite_false]
    · simp only [recV, Hashes.withTable, h5, hk, ite_false]
  have hv : @vPre (icPrg (rowFn E)) (recV p Hb G2' G5) CrtGen.tables st =
      @vPre (icPrg (rowFn E)) (recV p Hb G2 G5) CrtGen.tables st :=
    @vPre_agreeOff (icPrg (rowFn E)) _ _ _ unread_h23 hA _ _
  refine @verify_h23_congr (icPrg (rowFn E)) _ _ hA _ _ _ ?_
  rw [hv]
  simp only [recV, Hashes.withTable, reduceCtorEq, ite_true, ite_false]
  split_ifs with hx
  · congr 2
    exact hk _ hx.choose_spec
  · rfl

/-- **The keys the Lean simulator's programming changes** are grinding keys of the prefix it
recomputes from its simulated proof (`outPre`, on the tables' `H₅` and cipher). -/
theorem progRO_moved (Hb : Hashes) (st : Statement) (c : SimCoins p) (s : ShG R p) (k : K2 p)
    (hk : (progRO p Hb st c s).1 k ≠ s.1 k) :
    k.1 = blk (preLen p) (@outPre (icPrg (rowFn s.2.2)) Hb CrtGen.tables st s.2.1 (simulate p c)) := by
  by_contra hne
  apply hk
  refine programAt_apply_of_ne _ _ fun j hj => hne ?_
  rw [← hj]
  rfl

/-- **The verifier's `H₂³` point is a point where the tables differ.** -/
def HitPt (Hb : Hashes) (st : Statement) (proof : ByteArray) (s' s : ShG R p) : Prop :=
  ∃ k, enc2 p k = vPoint Hb st proof s ∧ s'.1 k ≠ s.1 k

/-- **The programming moves the verifier only at its `H₂³` point.** -/
theorem verRO_moved (Hb : Hashes) (st : Statement) (proof : ByteArray) (s' s : ShG R p)
    (h2 : s'.2 = s.2) (h : verRO p Hb st proof s' ≠ verRO p Hb st proof s) :
    HitPt Hb st proof s' s := by
  by_contra hn
  exact h (verRO_h23_eq Hb st proof s s' h2 fun k hk => by
    by_contra hne
    exact hn ⟨k, hk, hne⟩)

/-- The same for acceptance. -/
theorem verRO_accept_moved (Hb : Hashes) (st : Statement) (proof : ByteArray) (s' s : ShG R p)
    (h2 : s'.2 = s.2) (h' : (verRO p Hb st proof s').accept = true)
    (h : ¬ (verRO p Hb st proof s).accept = true) : HitPt Hb st proof s' s :=
  verRO_moved Hb st proof s' s h2 fun he => h (he ▸ h')

end Lean

end VoleMole.Theft
