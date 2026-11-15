import VoleMole.ZK.MainSharedLin

/-!
# The four-proof games on the linear hop (`lean/docs/zk.md` §4.2)

`main_sharedAll_le` (`ZK/MainSharedAll.lean`) is the joint hop for a game of four proofs in
sequence (`MainChain.Game`) with all tables shared (`realAll`, `simAll`). It reduces to the slice
game of `main_shared23_le` and pays `15·(εS + Δ23) + 15·Pr_sim[bstar]` and the probability that two
real proofs have one prefix. Moussaka 4(a), 4(b') and Ratatouille on `main` use it.

Here such a game is **restated as a `ZK.Sim.NGame` of four slots** (`toN`, witness lengths
`ns4`) and the linear hop `main_sharedAll_leLin` (`ZK/MainSharedLin.lean`) is applied to it:

* **The real games agree** (`realAll_eq_hybN`): `realAll`'s tape is the `NGame`'s tape with four
  unused `H₃` slices and three unused raw `H₂³` tables (`tapeEquiv4`), and on the used components
  the two views agree up to the slices (`gvN`, `hybVAll_gvN`), which the events ignore (`RdH`'s
  `i₁ … i₄`). Likewise `simAll` is the all-simulated hybrid (`simAll_eq_hybN`).
* **The reads carry over** (`rdN_of_rdH`), and `bstarN` of the four-slot `NGame` implies `bstar`
  of the four-proof game (`bstarN_imp`).
* **`main_sharedAll_le4Lin`**: for an event `F` with consistent reads (`RdH`),

      |Pr[all real; F] − Pr[all simulated; F]|
          ≤ 8·(εS(2q₃ + 4, 2q_E + 8·4607) + Δ23N(d, 4)) + Pr[all simulated; bstar].

  The factor `15` on `εS + Δ23` becomes `8`, the factor `15` on the bad event becomes `1`, and
  there is **no prefix-collision term**: the `NGame` hop counts the other proofs' `H₃` reads by
  their `ρ`.
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

/-! ## The game as an `NGame` -/

/-- **The witness lengths of the four slots.** -/
def ns4 (n₁ n₂ n₃ n₄ : ℕ) : Fin 4 → ℕ :=
  Fin.cases (motive := fun _ => ℕ) n₁ (Fin.cases (motive := fun _ => ℕ) n₂
    (Fin.cases (motive := fun _ => ℕ) n₃ fun _ => n₄))

section Four

variable {S : Type} {p₀ : Params} {n₁ n₂ n₃ n₄ : ℕ}

/-- **A four-proof game as an `NGame`**: slot `i`'s statement from the secret and the outputs of
the earlier slots. -/
def toN (G : Game S Out SW SW SW SW) : NGame S 4 :=
  ⟨Fin.cases (motive := fun _ => S → (Fin 4 → Option Out) → Option SW) (fun s _ => G.σ₁ s)
    (Fin.cases (motive := fun _ => S → (Fin 4 → Option Out) → Option SW)
      (fun s os => G.σ₂ s (os 0))
      (Fin.cases (motive := fun _ => S → (Fin 4 → Option Out) → Option SW)
        (fun s os => G.σ₃ s (os 0) (os 1)) fun _ s os => G.σ₄ s (os 0) (os 1) (os 2)))⟩

/-- **The four-proof view of an `NGame` view**: the outputs of the four slots, the programmed
`H₂³` table for every slot, and zero `H₃` slices (which the events of `main_sharedAll_le`
ignore). -/
def gvN (v : NView S 4 p₀) : GView S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) :=
  ⟨v.s, v.u, v.os 0, v.os 1, v.os 2, v.os 3, (fun _ => 0, v.M), (fun _ => 0, v.M),
    (fun _ => 0, v.M), (fun _ => 0, v.M)⟩

/-- The view with its four `H₃` slices replaced. -/
def GView.with3 {p₁ p₂ p₃ p₄ : Params} (v : GView S p₁ p₂ p₃ p₄) (g₁ g₂ g₃ g₄ : Tab3) :
    GView S p₁ p₂ p₃ p₄ :=
  (((v.with3₁ g₁).with3₂ g₂).with3₃ g₃).with3₄ g₄

/-- The coins of the four slots as the `NGame`'s coins. -/
def coins4 (k₁ : Bytes 16 × SimCoins (pw p₀ n₁)) (k₂ : Bytes 16 × SimCoins (pw p₀ n₂))
    (k₃ : Bytes 16 × SimCoins (pw p₀ n₃)) (k₄ : Bytes 16 × SimCoins (pw p₀ n₄)) :
    CoinsN p₀ (ns4 n₁ n₂ n₃ n₄) :=
  Fin.cases (motive := fun i => Bytes 16 × SimCoins (pw p₀ (ns4 n₁ n₂ n₃ n₄ i))) k₁
    (Fin.cases (motive := fun i => Bytes 16 × SimCoins (pw p₀ (ns4 n₁ n₂ n₃ n₄ i.succ))) k₂
      (Fin.cases (motive := fun i => Bytes 16 × SimCoins (pw p₀ (ns4 n₁ n₂ n₃ n₄ i.succ.succ))) k₃
        fun _ => k₄))

/-- **The `NGame`'s tape** of a tape of the four-proof game and an `H₃` table. -/
def toNT (z : GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) × H3T) :
    NTape p₀ (ns4 n₁ n₂ n₃ n₄) S :=
  (z.1.1, coins4 z.1.2.2.1.1 z.1.2.2.2.1.1 z.1.2.2.2.2.1.1 z.1.2.2.2.2.2.1, z.2, z.1.2.1,
    z.1.2.2.1.2.2)

/-- The components of the four-proof tape that the game does not read: the four `H₃` slices and
the raw `H₂³` tables of slots `2 … 4`. -/
abbrev Junk4 (p₂ p₃ p₄ : Params) := (Tab3 × Tab3 × Tab3 × Tab3) × Tab2G p₂ × Tab2G p₃ × Tab2G p₄

/-- **The four-proof tape with `H₃` is the `NGame`'s tape and the unused components.** -/
def tapeEquiv4 : GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) × H3T ≃
    NTape p₀ (ns4 n₁ n₂ n₃ n₄) S × Junk4 (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) where
  toFun z := (toNT z, ((z.1.2.2.1.2.1, z.1.2.2.2.1.2.1, z.1.2.2.2.2.1.2.1, z.1.2.2.2.2.2.2.1),
    z.1.2.2.2.1.2.2, z.1.2.2.2.2.1.2.2, z.1.2.2.2.2.2.2.2))
  invFun w := ((w.1.1, w.1.2.2.2.1, ((w.1.2.1 0, (w.2.1.1, w.1.2.2.2.2)),
      ((w.1.2.1 1, (w.2.1.2.1, w.2.2.1)), ((w.1.2.1 2, (w.2.1.2.2.1, w.2.2.2.1)),
        (w.1.2.1 3, (w.2.1.2.2.2, w.2.2.2.2)))))), w.1.2.2.1)
  left_inv z := rfl
  right_inv w := by
    obtain ⟨⟨s, cs, T, u, G2⟩, j⟩ := w
    refine Prod.ext (Prod.ext rfl (Prod.ext ?_ rfl)) rfl
    funext i
    refine Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun i => ?_) i) i) i
    rw [Fin.fin_one_eq_zero i]
    rfl

variable (Hb : Hashes) (G : Game S Out SW SW SW SW)

/-- **The real view of the four-proof game is the `NGame`'s**, up to the `H₃` slices. -/
theorem hybVAll_gvN (x : GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄)) (T : H3T) :
    hybVAll Hb G x T = (gvN (hybVN Hb p₀ (ns4 n₁ n₂ n₃ n₄) (toN G) 0 (toNT (x, T)))).with3
      (g3T₁ x) (g3T₂ x) (g3T₃ x) (g3T₄ x) := by
  rfl

/-- **The simulated view of the four-proof game is the `NGame`'s**, up to the `H₃` slices. -/
theorem hybV23_gvN (x : GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄)) (T : H3T) :
    hybV23 Hb G true true true true x =
      (gvN (hybVN Hb p₀ (ns4 n₁ n₂ n₃ n₄) (toN G) 4 (toNT (x, T)))).with3
      (g3T₁ x) (g3T₂ x) (g3T₃ x) (g3T₄ x) := by
  rfl

/-- **An event that ignores the `H₃` slices of the view.** -/
def NoSl (F : GView S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) → H3T → Prop) : Prop :=
  ∀ v T g₁ g₂ g₃ g₄, F (v.with3 g₁ g₂ g₃ g₄) T ↔ F v T

lemma noSl_of {F : GView S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) → H3T → Prop}
    (i₁ : ∀ v T G3, F (v.with3₁ G3) T = F v T) (i₂ : ∀ v T G3, F (v.with3₂ G3) T = F v T)
    (i₃ : ∀ v T G3, F (v.with3₃ G3) T = F v T) (i₄ : ∀ v T G3, F (v.with3₄ G3) T = F v T) :
    NoSl F := fun v T g₁ g₂ g₃ g₄ => by
  unfold GView.with3
  rw [i₄, i₃, i₂, i₁]

/-- The event of the `NGame` view. -/
def evN (F : GView S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) → H3T → Prop)
    (v : NView S 4 p₀) : Prop :=
  F (gvN v) v.T

variable [Fintype S] [Nonempty S]

/-- Integrating an event of the `NGame`'s tape over the four-proof tape and `H₃`. -/
theorem pr_toNT (Φ : NTape p₀ (ns4 n₁ n₂ n₃ n₄) S → Prop) :
    pr (GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) × H3T) (fun z => Φ (toNT z)) =
      pr (NTape p₀ (ns4 n₁ n₂ n₃ n₄) S) Φ := by
  calc pr (GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) × H3T) (fun z => Φ (toNT z))
      = pr (GTape S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) × H3T)
          (fun z => Φ (tapeEquiv4 z).1) := rfl
    _ = pr (NTape p₀ (ns4 n₁ n₂ n₃ n₄) S × Junk4 (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄))
          (fun w => Φ w.1) := pr_equiv tapeEquiv4 (fun w => Φ w.1)
    _ = pr (NTape p₀ (ns4 n₁ n₂ n₃ n₄) S) Φ := pr_prod_fst Φ

/-- **The real four-proof game is hybrid `0` of the `NGame`.** -/
theorem realAll_eq_hybN {F : GView S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) → H3T → Prop}
    (hF : NoSl F) :
    realAll Hb G F = hybN Hb p₀ (ns4 n₁ n₂ n₃ n₄) (toN G) 0 (evN F) := by
  unfold realAll hybN
  rw [← pr_toNT]
  refine pr_congr fun z => ?_
  rw [hybVAll_gvN Hb G z.1 z.2, hF]
  rfl

/-- **The simulated four-proof game is hybrid `4` of the `NGame`.** -/
theorem simAll_eq_hybN {F : GView S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) → H3T → Prop}
    (hF : NoSl F) :
    simAll Hb G F = hybN Hb p₀ (ns4 n₁ n₂ n₃ n₄) (toN G) 4 (evN F) := by
  unfold simAll hybN
  rw [← pr_toNT]
  refine pr_congr fun z => ?_
  rw [hybV23_gvN Hb G z.1 z.2, hF]
  rfl

/-! ## The reads, the bad event, validity -/

omit [Fintype S] [Nonempty S] in
/-- **The reads of an event carry over to the `NGame` view.** -/
theorem rdN_of_rdH {X : Sort*} {F : GView S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) → H3T → X}
    {R5 : GView S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) → H3T → Finset (Bytes 37)}
    {q3 qE : ℕ} (h : RdH F R5 q3 qE) :
    RdN (fun v : NView S 4 p₀ => F (gvN v) v.T) (fun v => R5 (gvN v) v.T) q3 qE := by
  obtain ⟨QE, hQEc, hQE⟩ := h.hE
  obtain ⟨QT, hQTc, hQT⟩ := h.hT
  exact ⟨fun v G5 hk => h.h5 (gvN v) v.T G5 hk,
    ⟨fun v => QE (gvN v) v.T, fun v => hQEc _ _, fun v E hk => hQE (gvN v) v.T E hk⟩,
    ⟨fun v => QT (gvN v) v.T, fun v => hQTc _ _, fun v T' hk => hQT (gvN v) v.T T' hk⟩⟩

omit [Fintype S] [Nonempty S] in
lemma noSl_of_rdH {X : Sort*} {F : GView S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) → H3T → X}
    {R5 : GView S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) → H3T → Finset (Bytes 37)}
    {q3 qE : ℕ} (h : RdH F R5 q3 qE) :
    ∀ v T g₁ g₂ g₃ g₄, F (v.with3 g₁ g₂ g₃ g₄) T = F v T := fun v T g₁ g₂ g₃ g₄ => by
  unfold GView.with3
  rw [h.i₄, h.i₃, h.i₂, h.i₁]

section Stmts

variable (v : NView S 4 p₀)

omit [Fintype S] [Nonempty S]
lemma yN_toN0 : yN (toN G) 0 v = G.σ₁ v.s := rfl
lemma yN_toN1 : yN (toN G) 1 v = G.σ₂ v.s (v.os 0) := rfl
lemma yN_toN2 : yN (toN G) 2 v = G.σ₃ v.s (v.os 0) (v.os 1) := rfl
lemma yN_toN3 : yN (toN G) 3 v = G.σ₄ v.s (v.os 0) (v.os 1) (v.os 2) := rfl

end Stmts

omit [Fintype S] [Nonempty S] in
lemma fin4_cases (j : Fin 4) : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by
  revert j; decide

omit [Fintype S] [Nonempty S] in
set_option maxHeartbeats 1000000 in
/-- **`bstarN` of the four-slot `NGame` is `bstar` of the four-proof game.** -/
theorem bstarN_imp (R5 : GView S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) → H3T →
      Finset (Bytes 37)) (v : NView S 4 p₀)
    (h : bstarN Hb (toN G) (fun i => pw p₀ (ns4 n₁ n₂ n₃ n₄ i)) (fun v => R5 (gvN v) v.T) v) :
    bstar Hb G (fun w => R5 w v.T) (gvN v) := by
  classical
  unfold bstar bstarCore
  unfold bstarN at h
  rcases h with ⟨i, he⟩ | ⟨j, hz | ⟨k, hk, hhit⟩⟩
  · rcases fin4_cases i with rfl | rfl | rfl | rfl
    · exact Or.inl (Or.inl he)
    · exact Or.inl (Or.inr (Or.inl he))
    · exact Or.inl (Or.inr (Or.inr (Or.inl he)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr he)))
  · rcases fin4_cases j with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl (Or.inl hz))
    · exact Or.inr (Or.inr (Or.inl (Or.inl hz)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl hz))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hz))))
  · rcases mem_union.1 hk with hR | hO
    · rcases fin4_cases j with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inl (Or.inr ⟨k, mem_union_left _ hR, hhit⟩))
      · exact Or.inr (Or.inr (Or.inl (Or.inr ⟨k, mem_union_left _ hR, hhit⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr ⟨k, mem_union_left _ hR, hhit⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨k, mem_union_left _ hR, hhit⟩))))
    · obtain ⟨m, hm, hkm⟩ := mem_biUnion.1 hO
      have hmj : m ≠ j := (mem_filter.1 hm).2
      rcases fin4_cases j with rfl | rfl | rfl | rfl <;>
        rcases fin4_cases m with rfl | rfl | rfl | rfl <;>
        first
        | exact absurd rfl hmj
        | exact Or.inr (Or.inl (Or.inr ⟨k, mem_union_right _ (mem_union_left _ (mem_union_left _ hkm)), hhit⟩))
        | exact Or.inr (Or.inl (Or.inr ⟨k, mem_union_right _ (mem_union_left _ (mem_union_right _ hkm)), hhit⟩))
        | exact Or.inr (Or.inl (Or.inr ⟨k, mem_union_right _ (mem_union_right _ hkm), hhit⟩))
        | exact Or.inr (Or.inr (Or.inl (Or.inr ⟨k, mem_union_right _ (mem_union_left _ (mem_union_left _ hkm)), hhit⟩)))
        | exact Or.inr (Or.inr (Or.inl (Or.inr ⟨k, mem_union_right _ (mem_union_left _ (mem_union_right _ hkm)), hhit⟩)))
        | exact Or.inr (Or.inr (Or.inl (Or.inr ⟨k, mem_union_right _ (mem_union_right _ hkm), hhit⟩)))
        | exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr ⟨k, mem_union_right _ (mem_union_left _ (mem_union_left _ hkm)), hhit⟩))))
        | exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr ⟨k, mem_union_right _ (mem_union_left _ (mem_union_right _ hkm)), hhit⟩))))
        | exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr ⟨k, mem_union_right _ (mem_union_right _ hkm), hhit⟩))))
        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨k, mem_union_right _ (mem_union_left _ (mem_union_left _ hkm)), hhit⟩))))
        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨k, mem_union_right _ (mem_union_left _ (mem_union_right _ hkm)), hhit⟩))))
        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨k, mem_union_right _ (mem_union_right _ hkm), hhit⟩))))

theorem nvalid_toN (hm₁ : MainP (pw p₀ n₁)) (hm₂ : MainP (pw p₀ n₂))
    (hm₃ : MainP (pw p₀ n₃)) (hm₄ : MainP (pw p₀ n₄)) (hp₁ : SmallParams (pw p₀ n₁))
    (hp₂ : SmallParams (pw p₀ n₂)) (hp₃ : SmallParams (pw p₀ n₃)) (hp₄ : SmallParams (pw p₀ n₄))
    (hv : GValid G (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄)) :
    NValid (toN G) p₀ (ns4 n₁ n₂ n₃ n₄) where
  v i s os y hy := by
    revert y
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.cases ?_ (fun _ => ?_) i) i) i
    · exact hv.v₁ s
    · exact hv.v₂ s (os 0)
    · exact hv.v₃ s (os 0) (os 1)
    · exact hv.v₄ s (os 0) (os 1) (os 2)
  m i := Fin.cases hm₁ (fun i => Fin.cases hm₂ (fun i => Fin.cases hm₃ (fun _ => hm₄) i) i) i
  sm i := Fin.cases hp₁ (fun i => Fin.cases hp₂ (fun i => Fin.cases hp₃ (fun _ => hp₄) i) i) i

/-! ## The result -/

/-- **The joint zero-knowledge hop on `main` for four proofs, linear**: all tables shared (one
`H₃`, one `H₂³` table, one `H₅` table, one cipher), four proofs in sequence of one QuickSilver
degree. For an event `F` of the view and of `H₃` with consistent reads (`RdH`: `H₅` at `R5`, the
cipher at `q_E` keys, `H₃` at `q₃` points),

    |Pr[all real; F] − Pr[all simulated; F]|
        ≤ 8·(εS(2q₃ + 4, 2q_E + 8·4607) + Δ23N(d, 4)) + Pr[all simulated; bstar].

Compared with `main_sharedAll_le`: the factor `15` on `εS + Δ23` becomes `8`, the factor `15` on
the bad event becomes `1`, and there is no prefix-collision term. -/
theorem main_sharedAll_le4Lin (hm₁ : MainP (pw p₀ n₁)) (hm₂ : MainP (pw p₀ n₂))
    (hm₃ : MainP (pw p₀ n₃)) (hm₄ : MainP (pw p₀ n₄)) (hp₁ : SmallParams (pw p₀ n₁))
    (hp₂ : SmallParams (pw p₀ n₂)) (hp₃ : SmallParams (pw p₀ n₃)) (hp₄ : SmallParams (pw p₀ n₄))
    (hHb : HashesWF Hb) (hv : GValid G (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄))
    (F : GView S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) → H3T → Prop)
    (R5 : GView S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) → H3T → Finset (Bytes 37))
    {q3 qE : ℕ} (hF : RdH F R5 q3 qE) (hR : RdH R5 R5 q3 qE) :
    |realAll Hb G F - simAll Hb G F| ≤
      8 * (εS (2 * q3 + 4) (2 * qE + 8 * 4607) + Δ23N p₀.qsDegree 4) +
        simAll Hb G (fun v T => bstar Hb G (fun v => R5 v T) v) := by
  have hNF : NoSl F := fun v T g₁ g₂ g₃ g₄ => by rw [noSl_of_rdH hF]
  have hNB : NoSl (fun v T => bstar Hb G (fun v => R5 v T) v) := fun v T g₁ g₂ g₃ g₄ => by
    show bstarCore Hb G _ _ _ _ _ _ (R5 (v.with3 g₁ g₂ g₃ g₄) T) ↔ _
    rw [noSl_of_rdH hR]; rfl
  have key := main_sharedAll_leLin (Hb := Hb) (p₀ := p₀) (ns := ns4 n₁ n₂ n₃ n₄) (G := toN G)
    hHb (nvalid_toN G hm₁ hm₂ hm₃ hm₄ hp₁ hp₂ hp₃ hp₄ hv) (evN F) (fun v => R5 (gvN v) v.T)
    (rdN_of_rdH hF) (rdN_of_rdH hR)
  have hb : hybN Hb p₀ (ns4 n₁ n₂ n₃ n₄) (toN G) 4
      (bstarN Hb (toN G) (fun i => pw p₀ (ns4 n₁ n₂ n₃ n₄ i)) (fun v => R5 (gvN v) v.T)) ≤
      simAll Hb G (fun v T => bstar Hb G (fun v => R5 v T) v) := by
    rw [simAll_eq_hybN Hb G hNB]
    exact pr_mono fun x hx => bstarN_imp Hb G R5 _ hx
  rw [realAll_eq_hybN Hb G hNF, simAll_eq_hybN Hb G hNF]
  have e : (2 : ℝ) * ((4 : ℕ) : ℝ) = 8 := by norm_num
  have e' : 2 * qE + 2 * 4 * 4607 = 2 * qE + 8 * 4607 := by norm_num
  rw [e, e'] at key
  linarith

end Four

end VoleMole.ZK.Sim
