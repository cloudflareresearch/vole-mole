import VoleMole.ZK.MainSlots

/-!
# Zero knowledge on `main` for four proofs in sequence, jointly (`lean/docs/zk.md` §4.1)

**`main_chain_le`**: in any game of four `main`-layout proofs in sequence (`Privacy.MainChain.Game`:
each statement and witness may depend on a secret and on the earlier proofs), with the executable
prover in the model of `zk_rom_ic` (each proof's own uniform tables; the adversary `F` sees the
proofs and every proof's `H₃`, `H₅` and cipher tables), replacing all four proofs by the
simulator costs at most

    4·(q₃·2⁻¹²⁸ + 221·(4607 + q_E)·2⁻¹²⁸) + 15·Pr[predAll]

where `F` reads each `H₃` table at `q₃` keys and each cipher table at `q_E` keys (`RdV`, with the
rest of the game fixed) and each `H₅` table at the keys `Rⱼ`, a **consistent** read set
(`VCons`), and `predAll` is the event, **in the game with all four proofs simulated**, that some
proof's witness prefix `w[0..16)` is among the candidates of its `H₅` read set (`predJ`). This is
the joint (PU) hop: H1–H4 per proof (`real_fill_close`), the identical-until-bad coupling of H5 and
H6 for the four proofs at once (`MainChain.fill_ideal_le`), the bad event turned into a prediction
on simulated proofs (`bad_predJ`, `ideal_sim_closeP`), and the last step per proof
(`ideal_sim_close`). Condition (PU) is then a bound on `Pr[predAll]`, a probability in a game in
which the witnesses enter only through the statements and the prefixes.
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

namespace VoleMole.ZK.Sim

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy
open VoleMole.Privacy.MainChain

attribute [local instance] decEqW128
attribute [local irreducible] simulate proveIdeal proveE firstHit

variable [HasPrg]

section Game

variable {S : Type} [Fintype S] [Nonempty S] (Hb : Hashes) (T : CrtTables)
  {p₁ p₂ p₃ p₄ : Params} (hm₁ : MainP p₁) (hm₂ : MainP p₂) (hm₃ : MainP p₃) (hm₄ : MainP p₄)

/-- **Consistent `H₅` read sets** of the adversary `F` (on the tables it sees): changing proof `j`'s
`H₅` table off `Rⱼ` changes neither `F` nor any read set. -/
structure VCons (F : Ev S Out (Vis p₁) (Vis p₂) (Vis p₃) (Vis p₄))
    (R₁ : RSet S Out (Vis p₁) (Vis p₂) (Vis p₃) (Vis p₄) (SKey p₁))
    (R₂ : RSet S Out (Vis p₁) (Vis p₂) (Vis p₃) (Vis p₄) (SKey p₂))
    (R₃ : RSet S Out (Vis p₁) (Vis p₂) (Vis p₃) (Vis p₄) (SKey p₃))
    (R₄ : RSet S Out (Vis p₁) (Vis p₂) (Vis p₃) (Vis p₄) (SKey p₄)) : Prop where
  c₁ : ∀ s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ (g : Tab5 p₁),
    (∀ k ∈ R₁ s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄, v₁.2.1 k = g k) →
    (F s o₁ o₂ o₃ o₄ (v₁.1, g, v₁.2.2) v₂ v₃ v₄ ↔ F s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄) ∧
    R₁ s o₁ o₂ o₃ o₄ (v₁.1, g, v₁.2.2) v₂ v₃ v₄ = R₁ s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ ∧
    R₂ s o₁ o₂ o₃ o₄ (v₁.1, g, v₁.2.2) v₂ v₃ v₄ = R₂ s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ ∧
    R₃ s o₁ o₂ o₃ o₄ (v₁.1, g, v₁.2.2) v₂ v₃ v₄ = R₃ s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ ∧
    R₄ s o₁ o₂ o₃ o₄ (v₁.1, g, v₁.2.2) v₂ v₃ v₄ = R₄ s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄
  c₂ : ∀ s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ (g : Tab5 p₂),
    (∀ k ∈ R₂ s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄, v₂.2.1 k = g k) →
    (F s o₁ o₂ o₃ o₄ v₁ (v₂.1, g, v₂.2.2) v₃ v₄ ↔ F s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄) ∧
    R₁ s o₁ o₂ o₃ o₄ v₁ (v₂.1, g, v₂.2.2) v₃ v₄ = R₁ s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ ∧
    R₂ s o₁ o₂ o₃ o₄ v₁ (v₂.1, g, v₂.2.2) v₃ v₄ = R₂ s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ ∧
    R₃ s o₁ o₂ o₃ o₄ v₁ (v₂.1, g, v₂.2.2) v₃ v₄ = R₃ s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ ∧
    R₄ s o₁ o₂ o₃ o₄ v₁ (v₂.1, g, v₂.2.2) v₃ v₄ = R₄ s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄
  c₃ : ∀ s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ (g : Tab5 p₃),
    (∀ k ∈ R₃ s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄, v₃.2.1 k = g k) →
    (F s o₁ o₂ o₃ o₄ v₁ v₂ (v₃.1, g, v₃.2.2) v₄ ↔ F s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄) ∧
    R₁ s o₁ o₂ o₃ o₄ v₁ v₂ (v₃.1, g, v₃.2.2) v₄ = R₁ s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ ∧
    R₂ s o₁ o₂ o₃ o₄ v₁ v₂ (v₃.1, g, v₃.2.2) v₄ = R₂ s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ ∧
    R₃ s o₁ o₂ o₃ o₄ v₁ v₂ (v₃.1, g, v₃.2.2) v₄ = R₃ s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ ∧
    R₄ s o₁ o₂ o₃ o₄ v₁ v₂ (v₃.1, g, v₃.2.2) v₄ = R₄ s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄
  c₄ : ∀ s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ (g : Tab5 p₄),
    (∀ k ∈ R₄ s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄, v₄.2.1 k = g k) →
    (F s o₁ o₂ o₃ o₄ v₁ v₂ v₃ (v₄.1, g, v₄.2.2) ↔ F s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄) ∧
    R₁ s o₁ o₂ o₃ o₄ v₁ v₂ v₃ (v₄.1, g, v₄.2.2) = R₁ s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ ∧
    R₂ s o₁ o₂ o₃ o₄ v₁ v₂ v₃ (v₄.1, g, v₄.2.2) = R₂ s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ ∧
    R₃ s o₁ o₂ o₃ o₄ v₁ v₂ v₃ (v₄.1, g, v₄.2.2) = R₃ s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄ ∧
    R₄ s o₁ o₂ o₃ o₄ v₁ v₂ v₃ (v₄.1, g, v₄.2.2) = R₄ s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄

/-- **The joint prediction**: some proof's witness prefix is a candidate of its `H₅` read set, on
the predictor's observations (`PObs`: in the simulated game, the simulator's shared tape, the
corrections and `d`). -/
def predAll (R₁ : RSet S Out (Vis p₁) (Vis p₂) (Vis p₃) (Vis p₄) (SKey p₁))
    (R₂ : RSet S Out (Vis p₁) (Vis p₂) (Vis p₃) (Vis p₄) (SKey p₂))
    (R₃ : RSet S Out (Vis p₁) (Vis p₂) (Vis p₃) (Vis p₄) (SKey p₃))
    (R₄ : RSet S Out (Vis p₁) (Vis p₂) (Vis p₃) (Vis p₄) (SKey p₄)) :
    Ev S Out (PObs p₁) (PObs p₂) (PObs p₃) (PObs p₄) :=
  fun s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ =>
    predJ Hb T hm₁ (R₁ s o₁ o₂ o₃ o₄ ω₁.2.1 ω₂.2.1 ω₃.2.1 ω₄.2.1) ω₁ ∨
    predJ Hb T hm₂ (R₂ s o₁ o₂ o₃ o₄ ω₁.2.1 ω₂.2.1 ω₃.2.1 ω₄.2.1) ω₂ ∨
    predJ Hb T hm₃ (R₃ s o₁ o₂ o₃ o₄ ω₁.2.1 ω₂.2.1 ω₃.2.1 ω₄.2.1) ω₃ ∨
    predJ Hb T hm₄ (R₄ s o₁ o₂ o₃ o₄ ω₁.2.1 ω₂.2.1 ω₃.2.1 ω₄.2.1) ω₄

variable {Hb T hm₁ hm₂ hm₃ hm₄}

/-- The adversary's read sets on the `mainH` observations. -/
def rsetsOf (R₁ : RSet S Out (Vis p₁) (Vis p₂) (Vis p₃) (Vis p₄) (SKey p₁))
    (R₂ : RSet S Out (Vis p₁) (Vis p₂) (Vis p₃) (Vis p₄) (SKey p₂))
    (R₃ : RSet S Out (Vis p₁) (Vis p₂) (Vis p₃) (Vis p₄) (SKey p₃))
    (R₄ : RSet S Out (Vis p₁) (Vis p₂) (Vis p₃) (Vis p₄) (SKey p₄)) :
    RSets (S := S) (O := Out) (mainH Hb T p₁ hm₁) (mainH Hb T p₂ hm₂) (mainH Hb T p₃ hm₃)
      (mainH Hb T p₄ hm₄) where
  r₁ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ := R₁ s o₁ o₂ o₃ o₄ (visOf Hb T hm₁ ω₁) (visOf Hb T hm₂ ω₂)
    (visOf Hb T hm₃ ω₃) (visOf Hb T hm₄ ω₄)
  r₂ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ := R₂ s o₁ o₂ o₃ o₄ (visOf Hb T hm₁ ω₁) (visOf Hb T hm₂ ω₂)
    (visOf Hb T hm₃ ω₃) (visOf Hb T hm₄ ω₄)
  r₃ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ := R₃ s o₁ o₂ o₃ o₄ (visOf Hb T hm₁ ω₁) (visOf Hb T hm₂ ω₂)
    (visOf Hb T hm₃ ω₃) (visOf Hb T hm₄ ω₄)
  r₄ s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ := R₄ s o₁ o₂ o₃ o₄ (visOf Hb T hm₁ ω₁) (visOf Hb T hm₂ ω₂)
    (visOf Hb T hm₃ ω₃) (visOf Hb T hm₄ ω₄)

/-- The adversary's event on the `mainH` observations. -/
def evOf (F : Ev S Out (Vis p₁) (Vis p₂) (Vis p₃) (Vis p₄)) :
    Ev S Out (mainH Hb T p₁ hm₁).Obs (mainH Hb T p₂ hm₂).Obs (mainH Hb T p₃ hm₃).Obs
      (mainH Hb T p₄ hm₄).Obs :=
  fun s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ => F s o₁ o₂ o₃ o₄ (visOf Hb T hm₁ ω₁) (visOf Hb T hm₂ ω₂)
    (visOf Hb T hm₃ ω₃) (visOf Hb T hm₄ ω₄)

/-- `VCons` on the tables is `Cons` on the `mainH` observations. -/
theorem VCons.cons {F : Ev S Out (Vis p₁) (Vis p₂) (Vis p₃) (Vis p₄)}
    {R₁ : RSet S Out (Vis p₁) (Vis p₂) (Vis p₃) (Vis p₄) (SKey p₁)}
    {R₂ : RSet S Out (Vis p₁) (Vis p₂) (Vis p₃) (Vis p₄) (SKey p₂)}
    {R₃ : RSet S Out (Vis p₁) (Vis p₂) (Vis p₃) (Vis p₄) (SKey p₃)}
    {R₄ : RSet S Out (Vis p₁) (Vis p₂) (Vis p₃) (Vis p₄) (SKey p₄)} (h : VCons F R₁ R₂ R₃ R₄) :
    Cons (evOf (Hb := Hb) (T := T) (hm₁ := hm₁) (hm₂ := hm₂) (hm₃ := hm₃) (hm₄ := hm₄) F)
      (rsetsOf R₁ R₂ R₃ R₄) := by
  refine ⟨fun s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ g hg => ?_, fun s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ g hg => ?_,
    fun s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ g hg => ?_, fun s o₁ o₂ o₃ o₄ ω₁ ω₂ ω₃ ω₄ g hg => ?_⟩
  · obtain ⟨e0, e1, e2, e3, e4⟩ := h.c₁ s o₁ o₂ o₃ o₄ _ _ _ _ g hg
    exact ⟨e0, by simp only [RSets.at, rsetsOf]; exact Prod.ext e1 (Prod.ext e2 (Prod.ext e3 e4))⟩
  · obtain ⟨e0, e1, e2, e3, e4⟩ := h.c₂ s o₁ o₂ o₃ o₄ _ _ _ _ g hg
    exact ⟨e0, by simp only [RSets.at, rsetsOf]; exact Prod.ext e1 (Prod.ext e2 (Prod.ext e3 e4))⟩
  · obtain ⟨e0, e1, e2, e3, e4⟩ := h.c₃ s o₁ o₂ o₃ o₄ _ _ _ _ g hg
    exact ⟨e0, by simp only [RSets.at, rsetsOf]; exact Prod.ext e1 (Prod.ext e2 (Prod.ext e3 e4))⟩
  · obtain ⟨e0, e1, e2, e3, e4⟩ := h.c₄ s o₁ o₂ o₃ o₄ _ _ _ _ g hg
    exact ⟨e0, by simp only [RSets.at, rsetsOf]; exact Prod.ext e1 (Prod.ext e2 (Prod.ext e3 e4))⟩

variable (Hb T hm₁ hm₂ hm₃ hm₄)

/-- **The joint zero-knowledge hop on `main`, for four proofs in sequence.** See the module
docstring. -/
theorem main_chain_le (G : Game S Out SW SW SW SW) (F : Ev S Out (Vis p₁) (Vis p₂) (Vis p₃) (Vis p₄))
    (R₁ : RSet S Out (Vis p₁) (Vis p₂) (Vis p₃) (Vis p₄) (SKey p₁))
    (R₂ : RSet S Out (Vis p₁) (Vis p₂) (Vis p₃) (Vis p₄) (SKey p₂))
    (R₃ : RSet S Out (Vis p₁) (Vis p₂) (Vis p₃) (Vis p₄) (SKey p₃))
    (R₄ : RSet S Out (Vis p₁) (Vis p₂) (Vis p₃) (Vis p₄) (SKey p₄)) (hc : VCons F R₁ R₂ R₃ R₄)
    (hs₁ : SmallParams p₁) (hs₂ : SmallParams p₂) (hs₃ : SmallParams p₃) (hs₄ : SmallParams p₄)
    (q3 qE : ℕ)
    (hB₁ : ∀ s o₁ o₂ o₃ o₄ v₂ v₃ v₄, RdV q3 qE fun v₁ => F s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄)
    (hB₂ : ∀ s o₁ o₂ o₃ o₄ v₁ v₃ v₄, RdV q3 qE fun v₂ => F s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄)
    (hB₃ : ∀ s o₁ o₂ o₃ o₄ v₁ v₂ v₄, RdV q3 qE fun v₃ => F s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄)
    (hB₄ : ∀ s o₁ o₂ o₃ o₄ v₁ v₂ v₃, RdV q3 qE fun v₄ => F s o₁ o₂ o₃ o₄ v₁ v₂ v₃ v₄)
    (hv₁ : ∀ s, ∀ y ∈ G.σ₁ s, ValidZK T p₁ y) (hv₂ : ∀ s o₁, ∀ y ∈ G.σ₂ s o₁, ValidZK T p₂ y)
    (hv₃ : ∀ s o₁ o₂, ∀ y ∈ G.σ₃ s o₁ o₂, ValidZK T p₃ y)
    (hv₄ : ∀ s o₁ o₂ o₃, ∀ y ∈ G.σ₄ s o₁ o₂ o₃, ValidZK T p₄ y) :
    |pr _ (ev G (realSlot Hb T p₁) (realSlot Hb T p₂) (realSlot Hb T p₃) (realSlot Hb T p₄) F) -
        pr _ (ev G (simSlot p₁) (simSlot p₂) (simSlot p₃) (simSlot p₄) F)| ≤
      4 * εRF q3 qE + 15 * pr _ (ev G (simP p₁) (simP p₂) (simP p₃) (simP p₄)
        (predAll Hb T hm₁ hm₂ hm₃ hm₄ R₁ R₂ R₃ R₄)) := by
  set H₁ := mainH Hb T p₁ hm₁
  set H₂ := mainH Hb T p₂ hm₂
  set H₃ := mainH Hb T p₃ hm₃
  set H₄ := mainH Hb T p₄ hm₄
  set fv₁ := H₁.fillS.mapObs (visOf Hb T hm₁)
  set fv₂ := H₂.fillS.mapObs (visOf Hb T hm₂)
  set fv₃ := H₃.fillS.mapObs (visOf Hb T hm₃)
  set fv₄ := H₄.fillS.mapObs (visOf Hb T hm₄)
  set iv₁ := H₁.idealS.mapObs (visOf Hb T hm₁)
  set iv₂ := H₂.idealS.mapObs (visOf Hb T hm₂)
  set iv₃ := H₃.idealS.mapObs (visOf Hb T hm₃)
  set iv₄ := H₄.idealS.mapObs (visOf Hb T hm₄)
  -- H1–H4 and the tape, one proof at a time.
  have a1 := hop₁ G (realSlot Hb T p₂) (realSlot Hb T p₃) (realSlot Hb T p₄) F
    (real_fill_close Hb T hm₁ hs₁ q3 qE) hv₁ fun s _ _ _ o => hB₁ s o _ _ _ _ _ _
  have a2 := hop₂ G fv₁ (realSlot Hb T p₃) (realSlot Hb T p₄) F
    (real_fill_close Hb T hm₂ hs₂ q3 qE) hv₂ fun s _ _ _ o => hB₂ s _ o _ _ _ _ _
  have a3 := hop₃ G fv₁ fv₂ (realSlot Hb T p₄) F
    (real_fill_close Hb T hm₃ hs₃ q3 qE) hv₃ fun s _ _ _ o => hB₃ s _ _ o _ _ _ _
  have a4 := hop₄ G fv₁ fv₂ fv₃ F
    (real_fill_close Hb T hm₄ hs₄ q3 qE) hv₄ fun s _ _ _ o => hB₄ s _ _ _ o _ _ _
  -- H5 → H6 for the four proofs at once.
  have h6 := fill_ideal_le G (H₁ := H₁) (H₂ := H₂) (H₃ := H₃) (H₄ := H₄) (Φ := evOf F) (R := rsetsOf R₁ R₂ R₃ R₄) (VCons.cons hc)
  have eF : pr _ (ev G fv₁ fv₂ fv₃ fv₄ F) =
      W (H₁ := H₁) (H₂ := H₂) (H₃ := H₃) (H₄ := H₄) G true true true true (evOf (Hb := Hb) (T := T) (hm₁ := hm₁) (hm₂ := hm₂) (hm₃ := hm₃) (hm₄ := hm₄) F) := rfl
  have eI : pr _ (ev G iv₁ iv₂ iv₃ iv₄ F) =
      W (H₁ := H₁) (H₂ := H₂) (H₃ := H₃) (H₄ := H₄) G false false false false (evOf (Hb := Hb) (T := T) (hm₁ := hm₁) (hm₂ := hm₂) (hm₃ := hm₃) (hm₄ := hm₄) F) := rfl
  -- The last step, one proof at a time.
  have b1 := hop₁ G iv₂ iv₃ iv₄ F (ideal_sim_close Hb T hm₁) hv₁ fun _ _ _ _ => trivial
  have b2 := hop₂ G (simSlot p₁) iv₃ iv₄ F (ideal_sim_close Hb T hm₂) hv₂ fun _ _ _ _ => trivial
  have b3 := hop₃ G (simSlot p₁) (simSlot p₂) iv₄ F (ideal_sim_close Hb T hm₃) hv₃
    fun _ _ _ _ => trivial
  have b4 := hop₄ G (simSlot p₁) (simSlot p₂) (simSlot p₃) F (ideal_sim_close Hb T hm₄) hv₄
    fun _ _ _ _ => trivial
  -- The bad event, as a prediction on simulated proofs.
  have c0 : W (H₁ := H₁) (H₂ := H₂) (H₃ := H₃) (H₄ := H₄) G false false false false
      (badAll (rsetsOf (Hb := Hb) (T := T) (hm₁ := hm₁) (hm₂ := hm₂) (hm₃ := hm₃) (hm₄ := hm₄) R₁ R₂ R₃ R₄)) ≤
      pr _ (ev G (idealP Hb T hm₁) (idealP Hb T hm₂) (idealP Hb T hm₃) (idealP Hb T hm₄)
        (predAll Hb T hm₁ hm₂ hm₃ hm₄ R₁ R₂ R₃ R₄)) := by
    refine pr_ev_withObs_mono G H₁.idealS H₂.idealS H₃.idealS H₄.idealS _ _ _ _ _ _ ?_
    intro s o₁ o₂ o₃ o₄ y₁ k₁ y₂ k₂ y₃ k₃ y₄ k₄ h
    rcases h with h | h | h | h
    · exact Or.inl (bad_predJ Hb T hm₁ _ y₁ k₁ h)
    · exact Or.inr (Or.inl (bad_predJ Hb T hm₂ _ y₂ k₂ h))
    · exact Or.inr (Or.inr (Or.inl (bad_predJ Hb T hm₃ _ y₃ k₃ h)))
    · exact Or.inr (Or.inr (Or.inr (bad_predJ Hb T hm₄ _ y₄ k₄ h)))
  have c1 := hop₁ G (idealP Hb T hm₂) (idealP Hb T hm₃) (idealP Hb T hm₄)
    (predAll Hb T hm₁ hm₂ hm₃ hm₄ R₁ R₂ R₃ R₄) (ideal_sim_closeP Hb T hm₁) hv₁ fun _ _ _ _ => trivial
  have c2 := hop₂ G (simP p₁) (idealP Hb T hm₃) (idealP Hb T hm₄)
    (predAll Hb T hm₁ hm₂ hm₃ hm₄ R₁ R₂ R₃ R₄) (ideal_sim_closeP Hb T hm₂) hv₂ fun _ _ _ _ => trivial
  have c3 := hop₃ G (simP p₁) (simP p₂) (idealP Hb T hm₄)
    (predAll Hb T hm₁ hm₂ hm₃ hm₄ R₁ R₂ R₃ R₄) (ideal_sim_closeP Hb T hm₃) hv₃ fun _ _ _ _ => trivial
  have c4 := hop₄ G (simP p₁) (simP p₂) (simP p₃)
    (predAll Hb T hm₁ hm₂ hm₃ hm₄ R₁ R₂ R₃ R₄) (ideal_sim_closeP Hb T hm₄) hv₄ fun _ _ _ _ => trivial
  rw [← eF, ← eI] at h6
  have := abs_sub_le_iff.1 a1; have := abs_sub_le_iff.1 a2; have := abs_sub_le_iff.1 a3
  have := abs_sub_le_iff.1 a4; have := abs_sub_le_iff.1 h6; have := abs_sub_le_iff.1 b1
  have := abs_sub_le_iff.1 b2; have := abs_sub_le_iff.1 b3; have := abs_sub_le_iff.1 b4
  have := abs_sub_le_iff.1 c1; have := abs_sub_le_iff.1 c2; have := abs_sub_le_iff.1 c3
  have := abs_sub_le_iff.1 c4
  rw [abs_sub_le_iff]
  constructor <;> linarith

end Game

end VoleMole.ZK.Sim
