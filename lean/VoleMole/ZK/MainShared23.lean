import VoleMole.ZK.CollideMain

/-!
# The joint hop on `main` with one shared `H₂³` table (`lean/docs/zk.md` §4.2)

`main_shared_le` (`ZK/MainSharedGame.lean`) replaces four `main`-layout proofs by simulated ones
when they share the `H₅` table and the cipher, each proof keeping its own `H₂³` table. Here the
four proofs also **share the `H₂³` table**, as in the scheme: one table on every grinding point,
read by the real provers and programmed by the simulators. Each proof keeps its own `H₃` slice.

## The game (`viewOf23`)

Each slot is a behaviour (`SB`): its output on a statement and the tables it reads, its
programming of `H₂³` (`pg`: the identity for a real proof), its `H₃` slice, and the keys at which
it reads the shared `H₅` table and cipher. The slots run in sequence; slot `k` reads the `H₂³`
table **with the programmings of the earlier slots applied, the earliest outermost**
(`pg₁ (pg₂ (… G2))`), and the adversary sees the table with all four programmings applied in
that order. With all proofs real nothing is programmed and every proof reads the one raw table;
with all proofs simulated nothing reads `H₂³` and the table is the raw one programmed at the four
simulated proofs' grinding points (the earliest wins). The view is a `GView` whose four `H₂³`
components are that one table, so the events, read sets and the bad event `bstar` of
`ZK/MainSharedGame.lean` apply unchanged.

The shared raw `H₂³` table is the first slot's tape component (`GTape`: the other slots' `H₂³`
components are unused), so the hybrids live on the tape of `main_shared_le`.

## The hop (`hop23₁` … `hop23₄`)

Replacing slot `j` is `ctx_hop` (the one-proof theorem for the distinguisher "the rest of the
game") plus a **programming-collision term**: in the hybrid the real proof `j` reads the table
programmed by the earlier simulations (`L G2`), in the one-proof theorem the raw table. The two
real proofs differ only if proof `j`'s grinding prefix block is a programmed one, i.e. its tail is
the uniform `ã` of an earlier simulation (`SB.Tl`). `pr_collide_main` bounds this by

    Δ23 = 2⁻¹¹³ + εS(0, 4607) + 313·2⁻¹²⁸ + noHitProb + 3·2^(−8·16(d−1)),

`d` the QuickSilver degree (`2^(−1024)` for `d = 9`). The order of the programmings makes the
simulated side of the one-proof theorem (the replaced proof's programming applied first, the
earlier ones on top) exactly the next hybrid.

## The result (`main_shared23_le`)

    |Pr[all real; F] − Pr[all simulated; F]|
        ≤ 15·(εS(q₃, q_E + 8·4607) + Δ23) + 15·Pr[all simulated; bstar]

for an event `F` with consistent reads (`Rd F R5`, `Rd R5 R5`), the four proofs' parameters of
one QuickSilver degree (`pw p₀ n`: the parameters `p₀` with `n` witness bytes).
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

/-- **The parameters `p` with `n` witness bytes.** Proofs with parameters `pw p n` for one `p`
have the same grinding-prefix length, so their `H₂³` tables have one type. -/
def pw (p : Params) (n : ℕ) : Params := { p with witnessBytes := n }

/-! ## Behaviours on a shared `H₂³` table -/

/-- **A slot's behaviour on the shared tables**: its output on a statement and the tables it
reads, its programming of `H₂³` (given the statement and the shared `H₅` table and cipher), its
`H₃` slice, the keys at which the run reads `H₅` and the cipher (`r5`, `rE`, at the tables it
reads) and those at which the programming reads them (`q5`, `qE`). -/
structure SB (p : Params) where
  run : SW → Sh p → Out
  pg : Option SW → USh → Tab2G p → Tab2G p
  g3 : Tab3
  r5 : Option SW → Sh p → Finset (Bytes 37)
  rE : Option SW → Sh p → Finset Blk
  q5 : Option SW → USh → Finset (Bytes 37)
  qE : Option SW → USh → Finset Blk

/-- **A behaviour reads the shared `H₅` table and cipher only at its keys** (at most `4607`
cipher keys in all), and reads and programs nothing without a statement. -/
structure SB.OK {p : Params} (b : SB p) : Prop where
  r5c : ∀ (y : Option SW) (t : Sh p) (G5 : Tab5F), (∀ k ∈ b.r5 y t, t.2.1 k = G5 k) →
    ∀ sw ∈ y, b.run sw (t.1, G5, t.2.2) = b.run sw t
  rEc : ∀ (y : Option SW) (t : Sh p) (E : Cipher), (∀ k ∈ b.rE y t, t.2.2 k = E k) →
    ∀ sw ∈ y, b.run sw (t.1, t.2.1, E) = b.run sw t
  q5c : ∀ (y : Option SW) (u : USh) (G5 : Tab5F), (∀ k ∈ b.q5 y u, u.1 k = G5 k) →
    b.pg y (G5, u.2) = b.pg y u
  qEc : ∀ (y : Option SW) (u : USh) (E : Cipher), (∀ k ∈ b.qE y u, u.2 k = E k) →
    b.pg y (u.1, E) = b.pg y u
  hE : ∀ (y : Option SW) (t : Sh p), (b.rE y t).card + (b.qE y t.2).card ≤ 4607
  r5none : ∀ t, b.r5 none t = ∅
  q5none : ∀ u, b.q5 none u = ∅

/-- **The programming changes only keys whose prefix block has its tail in `T`.** -/
def SB.Tl {p : Params} (b : SB p) (T : Finset ByteArray) : Prop :=
  ∀ (y : Option SW) (u : USh) (G2 : Tab2G p) (k : K2 p), preTail k.1 ∉ T → b.pg y u G2 k = G2 k

/-- **A behaviour's `H₅` keys are keys of its proof** (or it fails), on valid statements. -/
def SB.Cov (Hb : Hashes) {p : Params} (b : SB p) : Prop :=
  ∀ y, ValidZK CrtGen.tables p y → ∀ (t : Sh p), ∀ k ∈ b.r5 (some y) t ∪ b.q5 (some y) t.2,
    slotErr (some (b.run y t)) ∨ k ∈ slotKeys Hb p (some y) (some (b.run y t)) t.2.2

section Behs

variable (Hb : Hashes) (p : Params)

lemma progKeys5_snd (st : Statement) (o : Out) (G2 G2' : Tab2G p) (u : USh) :
    progKeys5 Hb st o ((G2, u) : Sh p) = progKeys5 Hb st o ((G2', u) : Sh p) := by
  unfold progKeys5; rfl

lemma progKeysE_snd (st : Statement) (o : Out) (G2 G2' : Tab2G p) (u : USh) :
    progKeysE Hb st o ((G2, u) : Sh p) = progKeysE Hb st o ((G2', u) : Sh p) := by
  unfold progKeysE; rfl

/-- **The real prover** with randomness `ρ` and slice `G3`: it reads `H₂³` and programs nothing. -/
noncomputable def realSB (ρ : Bytes 16) (G3 : Tab3) : SB p where
  run y t := realRO p Hb (withP y.1 p) y.2 ρ G3 t
  pg _ _ G2 := G2
  g3 := G3
  r5 y t := match y with
    | some y => realKeys5 p Hb (withP y.1 p) y.2 (ba ρ) G3 t
    | none => ∅
  rE y t := match y with
    | some y => realKeysE p Hb (withP y.1 p) y.2 (ba ρ) G3 t
    | none => ∅
  q5 _ _ := ∅
  qE _ _ := ∅

/-- **The simulator** with coins `c`: it programs `H₂³` at its proof's grinding points. -/
noncomputable def simSB (c : SimCoins p) (G3 : Tab3) : SB p where
  run _ _ := simulate p c
  pg y u G2 := match y with
    | some y => (progRO p Hb (withP y.1 p) c ((G2, u) : Sh p)).1
    | none => G2
  g3 := G3
  r5 _ _ := ∅
  rE _ _ := ∅
  q5 y u := match y with
    | some y => progKeys5 Hb (withP y.1 p) (simulate p c) ((Classical.arbitrary _, u) : Sh p)
    | none => ∅
  qE y u := match y with
    | some y => progKeysE Hb (withP y.1 p) (simulate p c) ((Classical.arbitrary _, u) : Sh p)
    | none => ∅

/-- **A fixed output and slice**, programming nothing. -/
def givenSB (o : Out) (G3 : Tab3) : SB p where
  run _ _ := o
  pg _ _ G2 := G2
  g3 := G3
  r5 _ _ := ∅
  rE _ _ := ∅
  q5 _ _ := ∅
  qE _ _ := ∅

variable {p}

lemma realSB_ok (hHb : HashesWF Hb) (ρ : Bytes 16) (G3 : Tab3) : (realSB Hb p ρ G3).OK where
  r5c y t G5 h sw hsw := by
    cases hsw
    exact realRO_congr5 p Hb (withP sw.1 p) sw.2 ρ G3 t G5 h
  rEc y t E h sw hsw := by
    cases hsw
    exact realRO_congrE p Hb (withP sw.1 p) sw.2 hHb ρ G3 t E h
  q5c _ _ _ _ := rfl
  qEc _ _ _ _ := rfl
  hE y t := by
    rcases y with _ | y
    · simp [realSB]
    · simpa [realSB] using card_realKeysE p Hb (withP y.1 p) y.2 (ba ρ) G3 t
  r5none _ := rfl
  q5none _ := rfl

lemma simSB_ok (c : SimCoins p) (G3 : Tab3) : (simSB Hb p c G3).OK where
  r5c _ _ _ _ _ _ := rfl
  rEc _ _ _ _ _ _ := rfl
  q5c y u G5 h := by
    rcases y with _ | y
    · rfl
    · funext G2
      refine progRO_congr5 Hb (withP y.1 p) c ((G2, u) : Sh p) G5 fun k hk => h k ?_
      show k ∈ progKeys5 Hb (withP y.1 p) (simulate p c) ((Classical.arbitrary _, u) : Sh p)
      rw [progKeys5_snd Hb p _ _ _ G2]; exact hk
  qEc y u E h := by
    rcases y with _ | y
    · rfl
    · funext G2
      refine progRO_congrE Hb (withP y.1 p) c ((G2, u) : Sh p) E fun k hk => h k ?_
      show k ∈ progKeysE Hb (withP y.1 p) (simulate p c) ((Classical.arbitrary _, u) : Sh p)
      rw [progKeysE_snd Hb p _ _ _ G2]; exact hk
  hE y t := by
    rcases y with _ | y
    · simp [simSB]
    · simpa [simSB] using card_progKeysE Hb (withP y.1 p) (simulate p c)
        ((Classical.arbitrary _, t.2) : Sh p)
  r5none _ := rfl
  q5none _ := rfl

lemma givenSB_ok (o : Out) (G3 : Tab3) : (givenSB p o G3).OK where
  r5c _ _ _ _ _ _ := rfl
  rEc _ _ _ _ _ _ := rfl
  q5c _ _ _ _ := rfl
  qEc _ _ _ _ := rfl
  hE _ _ := by simp [givenSB]
  r5none _ := rfl
  q5none _ := rfl

lemma realSB_tl (ρ : Bytes 16) (G3 : Tab3) : (realSB Hb p ρ G3).Tl ∅ := fun _ _ _ _ _ => rfl

lemma givenSB_tl (o : Out) (G3 : Tab3) : (givenSB p o G3).Tl ∅ := fun _ _ _ _ _ => rfl

lemma simSB_tl (hHb : HashesWF Hb) (c : SimCoins p) (G3 : Tab3) :
    (simSB Hb p c G3).Tl {simTail c} := by
  intro y u G2 k hk
  rcases y with _ | y
  · rfl
  · show (progRO p Hb (withP y.1 p) c ((G2, u) : Sh p)).1 k = G2 k
    refine (progRO_progAt (R := Blk → Blk) Hb (withP y.1 p) c).2 ((G2, u) : Sh p) k fun hm => hk ?_
    rw [Finset.mem_singleton] at hm ⊢
    rw [hm]
    exact preTail_simBlk (st := withP y.1 p) hHb rfl c _

lemma givenSB_cov (o : Out) (G3 : Tab3) : (givenSB p o G3).Cov Hb := fun _ _ _ k hk => by
  simp [givenSB] at hk

lemma simSB_cov (c : SimCoins p) (G3 : Tab3) : (simSB Hb p c G3).Cov Hb := by
  intro y hy t k hk
  have hk' : k ∈ progKeys5 Hb (withP y.1 p) (simulate p c) ((Classical.arbitrary _, t.2) : Sh p) := by
    simpa [simSB] using hk
  rw [progKeys5_snd Hb p _ _ _ t.1] at hk'
  exact simB_cov Hb c (G3, t.1) y hy t.2 k hk'

lemma realSB_cov (hm : MainP p) (hHb : HashesWF Hb) (ρ : Bytes 16) (G3 : Tab3) :
    (realSB Hb p ρ G3).Cov Hb := by
  intro y hy t k hk
  have hk' : k ∈ realKeys5 p Hb (withP y.1 p) y.2 (ba ρ) G3 t := by simpa [realSB] using hk
  exact realB_cov Hb hm hHb ρ (G3, t.1) y hy t.2 k hk'

end Behs

/-! ## The view of the game -/

section Game

variable {S : Type} {p₀ : Params} {n₁ n₂ n₃ n₄ : ℕ}
  (G : Game S Out SW SW SW SW)

/-- **The view of the game with a shared `H₂³` table**: the slots run in sequence, slot `k` on
the raw table `G2` with the earlier slots' programmings applied (the earliest outermost); the
adversary sees the table with all four programmings applied, as each slot's `H₂³` component. -/
def viewOf23 (s : S) (G2 : Tab2G (pw p₀ n₁)) (u : USh) (b₁ : SB (pw p₀ n₁)) (b₂ : SB (pw p₀ n₂))
    (b₃ : SB (pw p₀ n₃)) (b₄ : SB (pw p₀ n₄)) :
    GView S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) :=
  let y₁ := G.σ₁ s
  let o₁ := y₁.map (b₁.run · (G2, u))
  let y₂ := G.σ₂ s o₁
  let o₂ := y₂.map (b₂.run · (b₁.pg y₁ u G2, u))
  let y₃ := G.σ₃ s o₁ o₂
  let o₃ := y₃.map (b₃.run · (b₁.pg y₁ u (b₂.pg y₂ u G2), u))
  let y₄ := G.σ₄ s o₁ o₂ o₃
  let o₄ := y₄.map (b₄.run · (b₁.pg y₁ u (b₂.pg y₂ u (b₃.pg y₃ u G2)), u))
  let M := b₁.pg y₁ u (b₂.pg y₂ u (b₃.pg y₃ u (b₄.pg y₄ u G2)))
  ⟨s, u, o₁, o₂, o₃, o₄, (b₁.g3, M), (b₂.g3, M), (b₃.g3, M), (b₄.g3, M)⟩

/-- **The view is determined slot by slot**: behaviours (and shared `H₅` table and cipher) that
agree on the statements and the tables of a run give the same view, up to `H₅` and the cipher. -/
theorem viewOf23_agree (s : S) (G2 : Tab2G (pw p₀ n₁)) (u u' : USh)
    (b₁ b₁' : SB (pw p₀ n₁)) (b₂ b₂' : SB (pw p₀ n₂)) (b₃ b₃' : SB (pw p₀ n₃))
    (b₄ b₄' : SB (pw p₀ n₄))
    (h₁ : ∀ sw ∈ yv₁ G (viewOf23 G s G2 u b₁ b₂ b₃ b₄), b₁'.run sw (G2, u') = b₁.run sw (G2, u))
    (g₁ : b₁'.pg (yv₁ G (viewOf23 G s G2 u b₁ b₂ b₃ b₄)) u' =
      b₁.pg (yv₁ G (viewOf23 G s G2 u b₁ b₂ b₃ b₄)) u)
    (h₂ : ∀ sw ∈ yv₂ G (viewOf23 G s G2 u b₁ b₂ b₃ b₄),
      b₂'.run sw (b₁.pg (yv₁ G (viewOf23 G s G2 u b₁ b₂ b₃ b₄)) u G2, u') =
        b₂.run sw (b₁.pg (yv₁ G (viewOf23 G s G2 u b₁ b₂ b₃ b₄)) u G2, u))
    (g₂ : b₂'.pg (yv₂ G (viewOf23 G s G2 u b₁ b₂ b₃ b₄)) u' =
      b₂.pg (yv₂ G (viewOf23 G s G2 u b₁ b₂ b₃ b₄)) u)
    (h₃ : ∀ sw ∈ yv₃ G (viewOf23 G s G2 u b₁ b₂ b₃ b₄),
      b₃'.run sw (b₁.pg (yv₁ G (viewOf23 G s G2 u b₁ b₂ b₃ b₄)) u
        (b₂.pg (yv₂ G (viewOf23 G s G2 u b₁ b₂ b₃ b₄)) u G2), u') =
      b₃.run sw (b₁.pg (yv₁ G (viewOf23 G s G2 u b₁ b₂ b₃ b₄)) u
        (b₂.pg (yv₂ G (viewOf23 G s G2 u b₁ b₂ b₃ b₄)) u G2), u))
    (g₃ : b₃'.pg (yv₃ G (viewOf23 G s G2 u b₁ b₂ b₃ b₄)) u' =
      b₃.pg (yv₃ G (viewOf23 G s G2 u b₁ b₂ b₃ b₄)) u)
    (h₄ : ∀ sw ∈ yv₄ G (viewOf23 G s G2 u b₁ b₂ b₃ b₄),
      b₄'.run sw (b₁.pg (yv₁ G (viewOf23 G s G2 u b₁ b₂ b₃ b₄)) u
        (b₂.pg (yv₂ G (viewOf23 G s G2 u b₁ b₂ b₃ b₄)) u
          (b₃.pg (yv₃ G (viewOf23 G s G2 u b₁ b₂ b₃ b₄)) u G2)), u') =
      b₄.run sw (b₁.pg (yv₁ G (viewOf23 G s G2 u b₁ b₂ b₃ b₄)) u
        (b₂.pg (yv₂ G (viewOf23 G s G2 u b₁ b₂ b₃ b₄)) u
          (b₃.pg (yv₃ G (viewOf23 G s G2 u b₁ b₂ b₃ b₄)) u G2)), u))
    (g₄ : b₄'.pg (yv₄ G (viewOf23 G s G2 u b₁ b₂ b₃ b₄)) u' =
      b₄.pg (yv₄ G (viewOf23 G s G2 u b₁ b₂ b₃ b₄)) u)
    (f₁ : b₁'.g3 = b₁.g3) (f₂ : b₂'.g3 = b₂.g3) (f₃ : b₃'.g3 = b₃.g3) (f₄ : b₄'.g3 = b₄.g3) :
    viewOf23 G s G2 u' b₁' b₂' b₃' b₄' = (viewOf23 G s G2 u b₁ b₂ b₃ b₄).withU u' := by
  have e₁ : (G.σ₁ s).map (b₁'.run · (G2, u')) = (G.σ₁ s).map (b₁.run · (G2, u)) :=
    Option.map_congr fun sw hsw => h₁ sw hsw
  have g₁' : b₁'.pg (G.σ₁ s) u' = b₁.pg (G.σ₁ s) u := g₁
  have e₂ : (G.σ₂ s ((G.σ₁ s).map (b₁.run · (G2, u)))).map
        (b₂'.run · (b₁.pg (G.σ₁ s) u G2, u')) =
      (G.σ₂ s ((G.σ₁ s).map (b₁.run · (G2, u)))).map (b₂.run · (b₁.pg (G.σ₁ s) u G2, u)) :=
    Option.map_congr fun sw hsw => h₂ sw hsw
  have g₂' : b₂'.pg (G.σ₂ s ((G.σ₁ s).map (b₁.run · (G2, u)))) u' =
      b₂.pg (G.σ₂ s ((G.σ₁ s).map (b₁.run · (G2, u)))) u := g₂
  have e₃ : (G.σ₃ s ((G.σ₁ s).map (b₁.run · (G2, u)))
        ((G.σ₂ s ((G.σ₁ s).map (b₁.run · (G2, u)))).map (b₂.run · (b₁.pg (G.σ₁ s) u G2, u)))).map
        (b₃'.run · (b₁.pg (G.σ₁ s) u (b₂.pg (G.σ₂ s ((G.σ₁ s).map (b₁.run · (G2, u)))) u G2), u')) =
      (G.σ₃ s ((G.σ₁ s).map (b₁.run · (G2, u)))
        ((G.σ₂ s ((G.σ₁ s).map (b₁.run · (G2, u)))).map (b₂.run · (b₁.pg (G.σ₁ s) u G2, u)))).map
        (b₃.run · (b₁.pg (G.σ₁ s) u (b₂.pg (G.σ₂ s ((G.σ₁ s).map (b₁.run · (G2, u)))) u G2), u)) :=
    Option.map_congr fun sw hsw => h₃ sw hsw
  have g₃' : b₃'.pg (G.σ₃ s ((G.σ₁ s).map (b₁.run · (G2, u)))
        ((G.σ₂ s ((G.σ₁ s).map (b₁.run · (G2, u)))).map (b₂.run · (b₁.pg (G.σ₁ s) u G2, u)))) u' =
      b₃.pg (G.σ₃ s ((G.σ₁ s).map (b₁.run · (G2, u)))
        ((G.σ₂ s ((G.σ₁ s).map (b₁.run · (G2, u)))).map (b₂.run · (b₁.pg (G.σ₁ s) u G2, u)))) u :=
    g₃
  have e₄ : (G.σ₄ s ((G.σ₁ s).map (b₁.run · (G2, u)))
        ((G.σ₂ s ((G.σ₁ s).map (b₁.run · (G2, u)))).map (b₂.run · (b₁.pg (G.σ₁ s) u G2, u)))
        ((G.σ₃ s ((G.σ₁ s).map (b₁.run · (G2, u)))
          ((G.σ₂ s ((G.σ₁ s).map (b₁.run · (G2, u)))).map (b₂.run · (b₁.pg (G.σ₁ s) u G2, u)))).map
          (b₃.run · (b₁.pg (G.σ₁ s) u (b₂.pg (G.σ₂ s ((G.σ₁ s).map (b₁.run · (G2, u)))) u G2), u)))).map
        (b₄'.run · (b₁.pg (G.σ₁ s) u (b₂.pg (G.σ₂ s ((G.σ₁ s).map (b₁.run · (G2, u)))) u
          (b₃.pg (G.σ₃ s ((G.σ₁ s).map (b₁.run · (G2, u)))
            ((G.σ₂ s ((G.σ₁ s).map (b₁.run · (G2, u)))).map (b₂.run · (b₁.pg (G.σ₁ s) u G2, u))))
            u G2)), u')) =
      (G.σ₄ s ((G.σ₁ s).map (b₁.run · (G2, u)))
        ((G.σ₂ s ((G.σ₁ s).map (b₁.run · (G2, u)))).map (b₂.run · (b₁.pg (G.σ₁ s) u G2, u)))
        ((G.σ₃ s ((G.σ₁ s).map (b₁.run · (G2, u)))
          ((G.σ₂ s ((G.σ₁ s).map (b₁.run · (G2, u)))).map (b₂.run · (b₁.pg (G.σ₁ s) u G2, u)))).map
          (b₃.run · (b₁.pg (G.σ₁ s) u (b₂.pg (G.σ₂ s ((G.σ₁ s).map (b₁.run · (G2, u)))) u G2), u)))).map
        (b₄.run · (b₁.pg (G.σ₁ s) u (b₂.pg (G.σ₂ s ((G.σ₁ s).map (b₁.run · (G2, u)))) u
          (b₃.pg (G.σ₃ s ((G.σ₁ s).map (b₁.run · (G2, u)))
            ((G.σ₂ s ((G.σ₁ s).map (b₁.run · (G2, u)))).map (b₂.run · (b₁.pg (G.σ₁ s) u G2, u))))
            u G2)), u)) :=
    Option.map_congr fun sw hsw => h₄ sw hsw
  have g₄' : b₄'.pg (G.σ₄ s ((G.σ₁ s).map (b₁.run · (G2, u)))
        ((G.σ₂ s ((G.σ₁ s).map (b₁.run · (G2, u)))).map (b₂.run · (b₁.pg (G.σ₁ s) u G2, u)))
        ((G.σ₃ s ((G.σ₁ s).map (b₁.run · (G2, u)))
          ((G.σ₂ s ((G.σ₁ s).map (b₁.run · (G2, u)))).map (b₂.run · (b₁.pg (G.σ₁ s) u G2, u)))).map
          (b₃.run · (b₁.pg (G.σ₁ s) u (b₂.pg (G.σ₂ s ((G.σ₁ s).map (b₁.run · (G2, u)))) u G2), u))))
        u' =
      b₄.pg (G.σ₄ s ((G.σ₁ s).map (b₁.run · (G2, u)))
        ((G.σ₂ s ((G.σ₁ s).map (b₁.run · (G2, u)))).map (b₂.run · (b₁.pg (G.σ₁ s) u G2, u)))
        ((G.σ₃ s ((G.σ₁ s).map (b₁.run · (G2, u)))
          ((G.σ₂ s ((G.σ₁ s).map (b₁.run · (G2, u)))).map (b₂.run · (b₁.pg (G.σ₁ s) u G2, u)))).map
          (b₃.run · (b₁.pg (G.σ₁ s) u (b₂.pg (G.σ₂ s ((G.σ₁ s).map (b₁.run · (G2, u)))) u G2), u))))
        u := g₄
  simp only [viewOf23, GView.withU]
  rw [e₁, g₁', e₂, g₂', e₃, g₃', e₄, g₄', f₁, f₂, f₃, f₄]

/-- The `H₅` keys the four behaviours read in a run (the run at the table it reads, and the
programming). -/
def tr5 (s : S) (G2 : Tab2G (pw p₀ n₁)) (u : USh) (b₁ : SB (pw p₀ n₁)) (b₂ : SB (pw p₀ n₂))
    (b₃ : SB (pw p₀ n₃)) (b₄ : SB (pw p₀ n₄)) : Finset (Bytes 37) :=
  let v := viewOf23 G s G2 u b₁ b₂ b₃ b₄
  (b₁.r5 (yv₁ G v) (G2, u) ∪ b₁.q5 (yv₁ G v) u) ∪
  (b₂.r5 (yv₂ G v) (b₁.pg (yv₁ G v) u G2, u) ∪ b₂.q5 (yv₂ G v) u) ∪
  (b₃.r5 (yv₃ G v) (b₁.pg (yv₁ G v) u (b₂.pg (yv₂ G v) u G2), u) ∪ b₃.q5 (yv₃ G v) u) ∪
  (b₄.r5 (yv₄ G v) (b₁.pg (yv₁ G v) u (b₂.pg (yv₂ G v) u (b₃.pg (yv₃ G v) u G2)), u) ∪
    b₄.q5 (yv₄ G v) u)

/-- The cipher keys the four behaviours read in a run. -/
def trE (s : S) (G2 : Tab2G (pw p₀ n₁)) (u : USh) (b₁ : SB (pw p₀ n₁)) (b₂ : SB (pw p₀ n₂))
    (b₃ : SB (pw p₀ n₃)) (b₄ : SB (pw p₀ n₄)) : Finset Blk :=
  let v := viewOf23 G s G2 u b₁ b₂ b₃ b₄
  (b₁.rE (yv₁ G v) (G2, u) ∪ b₁.qE (yv₁ G v) u) ∪
  (b₂.rE (yv₂ G v) (b₁.pg (yv₁ G v) u G2, u) ∪ b₂.qE (yv₂ G v) u) ∪
  (b₃.rE (yv₃ G v) (b₁.pg (yv₁ G v) u (b₂.pg (yv₂ G v) u G2), u) ∪ b₃.qE (yv₃ G v) u) ∪
  (b₄.rE (yv₄ G v) (b₁.pg (yv₁ G v) u (b₂.pg (yv₂ G v) u (b₃.pg (yv₃ G v) u G2)), u) ∪
    b₄.qE (yv₄ G v) u)

lemma card_trE {b₁ : SB (pw p₀ n₁)} {b₂ : SB (pw p₀ n₂)} {b₃ : SB (pw p₀ n₃)} {b₄ : SB (pw p₀ n₄)}
    (k₁ : b₁.OK) (k₂ : b₂.OK) (k₃ : b₃.OK) (k₄ : b₄.OK) (s : S) (G2 : Tab2G (pw p₀ n₁)) (u : USh) :
    (trE G s G2 u b₁ b₂ b₃ b₄).card ≤ 4 * 4607 := by
  unfold trE
  dsimp only
  set v := viewOf23 G s G2 u b₁ b₂ b₃ b₄
  have a₁ := k₁.hE (yv₁ G v) (G2, u)
  have a₂ := k₂.hE (yv₂ G v) (b₁.pg (yv₁ G v) u G2, u)
  have a₃ := k₃.hE (yv₃ G v) (b₁.pg (yv₁ G v) u (b₂.pg (yv₂ G v) u G2), u)
  have a₄ := k₄.hE (yv₄ G v) (b₁.pg (yv₁ G v) u (b₂.pg (yv₂ G v) u (b₃.pg (yv₃ G v) u G2)), u)
  have c₁ := card_union_le (b₁.rE (yv₁ G v) (G2, u)) (b₁.qE (yv₁ G v) u)
  have c₂ := card_union_le (b₂.rE (yv₂ G v) (b₁.pg (yv₁ G v) u G2, u)) (b₂.qE (yv₂ G v) u)
  have c₃ := card_union_le (b₃.rE (yv₃ G v) (b₁.pg (yv₁ G v) u (b₂.pg (yv₂ G v) u G2), u))
    (b₃.qE (yv₃ G v) u)
  have c₄ := card_union_le
    (b₄.rE (yv₄ G v) (b₁.pg (yv₁ G v) u (b₂.pg (yv₂ G v) u (b₃.pg (yv₃ G v) u G2)), u))
    (b₄.qE (yv₄ G v) u)
  refine (card_union_le _ _).trans ?_
  refine (Nat.add_le_add_right ((card_union_le _ _).trans (Nat.add_le_add_right
    (card_union_le _ _) _)) _).trans ?_
  simp only at a₁ a₂ a₃ a₄
  omega

/-- **Changing the `H₅` table off the behaviours' keys** changes the view only in that table. -/
theorem viewOf23_G5 (s : S) (G2 : Tab2G (pw p₀ n₁)) (u : USh) {b₁ : SB (pw p₀ n₁)}
    {b₂ : SB (pw p₀ n₂)} {b₃ : SB (pw p₀ n₃)} {b₄ : SB (pw p₀ n₄)}
    (k₁ : b₁.OK) (k₂ : b₂.OK) (k₃ : b₃.OK) (k₄ : b₄.OK) (G5 : Tab5F)
    (h : ∀ k ∈ tr5 G s G2 u b₁ b₂ b₃ b₄, u.1 k = G5 k) :
    viewOf23 G s G2 (G5, u.2) b₁ b₂ b₃ b₄ = (viewOf23 G s G2 u b₁ b₂ b₃ b₄).withU (G5, u.2) :=
  viewOf23_agree G s G2 u (G5, u.2) b₁ b₁ b₂ b₂ b₃ b₃ b₄ b₄
    (k₁.r5c _ (G2, u) G5 fun k hk => h k (mem_union_left _ (mem_union_left _ (mem_union_left _
      (mem_union_left _ hk)))))
    (k₁.q5c _ u G5 fun k hk => h k (mem_union_left _ (mem_union_left _ (mem_union_left _
      (mem_union_right _ hk)))))
    (k₂.r5c _ (_, u) G5 fun k hk => h k (mem_union_left _ (mem_union_left _ (mem_union_right _
      (mem_union_left _ hk)))))
    (k₂.q5c _ u G5 fun k hk => h k (mem_union_left _ (mem_union_left _ (mem_union_right _
      (mem_union_right _ hk)))))
    (k₃.r5c _ (_, u) G5 fun k hk => h k (mem_union_left _ (mem_union_right _ (mem_union_left _ hk))))
    (k₃.q5c _ u G5 fun k hk => h k (mem_union_left _ (mem_union_right _ (mem_union_right _ hk))))
    (k₄.r5c _ (_, u) G5 fun k hk => h k (mem_union_right _ (mem_union_left _ hk)))
    (k₄.q5c _ u G5 fun k hk => h k (mem_union_right _ (mem_union_right _ hk)))
    rfl rfl rfl rfl

/-- **Changing the cipher off the behaviours' keys** changes the view only in that table. -/
theorem viewOf23_E (s : S) (G2 : Tab2G (pw p₀ n₁)) (u : USh) {b₁ : SB (pw p₀ n₁)}
    {b₂ : SB (pw p₀ n₂)} {b₃ : SB (pw p₀ n₃)} {b₄ : SB (pw p₀ n₄)}
    (k₁ : b₁.OK) (k₂ : b₂.OK) (k₃ : b₃.OK) (k₄ : b₄.OK) (E : Cipher)
    (h : ∀ k ∈ trE G s G2 u b₁ b₂ b₃ b₄, u.2 k = E k) :
    viewOf23 G s G2 (u.1, E) b₁ b₂ b₃ b₄ = (viewOf23 G s G2 u b₁ b₂ b₃ b₄).withU (u.1, E) :=
  viewOf23_agree G s G2 u (u.1, E) b₁ b₁ b₂ b₂ b₃ b₃ b₄ b₄
    (k₁.rEc _ (G2, u) E fun k hk => h k (mem_union_left _ (mem_union_left _ (mem_union_left _
      (mem_union_left _ hk)))))
    (k₁.qEc _ u E fun k hk => h k (mem_union_left _ (mem_union_left _ (mem_union_left _
      (mem_union_right _ hk)))))
    (k₂.rEc _ (_, u) E fun k hk => h k (mem_union_left _ (mem_union_left _ (mem_union_right _
      (mem_union_left _ hk)))))
    (k₂.qEc _ u E fun k hk => h k (mem_union_left _ (mem_union_left _ (mem_union_right _
      (mem_union_right _ hk)))))
    (k₃.rEc _ (_, u) E fun k hk => h k (mem_union_left _ (mem_union_right _ (mem_union_left _ hk))))
    (k₃.qEc _ u E fun k hk => h k (mem_union_left _ (mem_union_right _ (mem_union_right _ hk))))
    (k₄.rEc _ (_, u) E fun k hk => h k (mem_union_right _ (mem_union_left _ hk)))
    (k₄.qEc _ u E fun k hk => h k (mem_union_right _ (mem_union_right _ hk)))
    rfl rfl rfl rfl

end Game

/-! ## The programming-collision term of a hop -/

/-- **The programming-collision bound of one hop**: `pr_collide_main` with `|T| ≤ 3`. -/
noncomputable def Δ23 (d : ℕ) : ℝ :=
  1 / 2 ^ 113 + εS 0 4607 + ((312 : ℕ) + 1) / 2 ^ 128 + (noHitProb + 3 / 2 ^ (8 * (16 * (d - 1))))

lemma Δ23_nonneg (d : ℕ) : 0 ≤ Δ23 d := by
  unfold Δ23
  have := εS_nonneg 0 4607
  have : 0 ≤ noHitProb := pr_nonneg _
  positivity

/-- **A real proof on the table programmed by earlier simulations** (at blocks whose tails lie in
a set of at most three values) differs from the proof on the raw table with probability at most
`Δ23`, on a slot's tape. -/
theorem pr_collide_slot (Hb : Hashes) {p : Params} (hm : MainP p) (hp : SmallParams p)
    (hHb : HashesWF Hb) (y : SW) (hy : ValidZK CrtGen.tables p y) (L : USh → Tab2G p → Tab2G p)
    (T : Finset ByteArray) (hT : T.card ≤ 3)
    (hL : ∀ u G2 (k : K2 p), preTail k.1 ∉ T → L u G2 k = G2 k) :
    pr (USh × KS p) (fun z => realRO p Hb (withP y.1 p) y.2 z.2.1.1 z.2.2.1 ((L z.1 z.2.2.2, z.1) : Sh p) ≠
      realRO p Hb (withP y.1 p) y.2 z.2.1.1 z.2.2.1 (shOf z.2.2.2 z.1)) ≤ Δ23 p.qsDegree := by
  classical
  obtain ⟨cs, hzk⟩ := hy
  have key := pr_collide_main (st := withP y.1 p) (w := y.2) (Hb := Hb) hm hzk hHb hp
    (L := fun t => (L t.2 t.1, t.2)) (B := fun _ => univ.filter fun b => preTail b ∈ T)
    ⟨fun _ => rfl, fun t k hk => hL t.2 t.1 k (by simpa using hk)⟩ T (fun _ b hb => by simpa using hb)
  let e : ((Bytes 16 × Tab3) × Sh p) × SimCoins p ≃ USh × KS p :=
    { toFun := fun a => (a.1.2.2, ((a.1.1.1, a.2), (a.1.1.2, a.1.2.1)))
      invFun := fun z => (((z.2.1.1, z.2.2.1), (z.2.2.2, z.1)), z.2.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← pr_equiv e]
  refine (le_of_eq (pr_prod_fst (β := SimCoins p) (fun a : (Bytes 16 × Tab3) × Sh p =>
    realRO p Hb (withP y.1 p) y.2 a.1.1 a.1.2 ((L a.2.2 a.2.1, a.2.2) : Sh p) ≠
      realRO p Hb (withP y.1 p) y.2 a.1.1 a.1.2 a.2))).trans (key.trans ?_)
  unfold Δ23
  have h3 : (T.card : ℝ) ≤ 3 := by exact_mod_cast hT
  have : (T.card : ℝ) / 2 ^ (8 * (16 * (p.qsDegree - 1))) ≤ 3 / 2 ^ (8 * (16 * (p.qsDegree - 1))) := by
    gcongr
  linarith

/-! ## The bad event of a hop implies `bstar` -/

section Bad

variable {S : Type} {p₁ p₂ p₃ p₄ : Params} (Hb : Hashes) (G : Game S Out SW SW SW SW)

lemma cov23 {p : Params} {b : SB p} (hk : b.OK) (hc : b.Cov Hb) (y : Option SW)
    (hy : ∀ sw ∈ y, ValidZK CrtGen.tables p sw) (t : Sh p) {k : Bytes 37}
    (h : k ∈ b.r5 y t ∪ b.q5 y t.2) :
    slotErr (y.map (b.run · t)) ∨ k ∈ slotKeys Hb p y (y.map (b.run · t)) t.2.2 := by
  rcases y with _ | sw
  · rw [hk.r5none, hk.q5none] at h; simp at h
  · exact hc sw (hy sw rfl) t k h

set_option maxRecDepth 8000 in
lemma bad₁ (hm : MainP p₁) (R5 : GView S p₁ p₂ p₃ p₄ → Finset (Bytes 37))
    (v : GView S p₁ p₂ p₃ p₄) (y : SW) (c : SimCoins p₁) (Tr : Finset (Bytes 37))
    (hy' : G.σ₁ v.s = some y) (ho : v.o₁ = some (simulate p₁ c))
    (hT : ∀ k ∈ Tr, slotErr v.o₂ ∨ slotErr v.o₃ ∨ slotErr v.o₄ ∨
      k ∈ slotKeys Hb p₂ (yv₂ G v) v.o₂ v.u.2 ∪ slotKeys Hb p₃ (yv₃ G v) v.o₃ v.u.2 ∪
        slotKeys Hb p₄ (yv₄ G v) v.o₄ v.u.2)
    (hz : (letI : HasPrg := icPrg v.u.2
      wPre y.2 ∈ candidatesG Hb CrtGen.tables (withP y.1 p₁) enc5 hm (R5 v ∪ Tr) c.1 c.2)) :
    bstar Hb G R5 v := by
  show bstarCore Hb G v.s v.o₁ v.o₂ v.o₃ v.o₄ v.u.2 (R5 v)
  rcases @pred_imp Hb (icPrg v.u.2) p₁ hm y c _ hz with h | h | h
  · exact Or.inl (Or.inl (ho ▸ h))
  · refine Or.inr (Or.inl (Or.inl ?_))
    rw [hy', ho]; exact h
  · have h' : ∃ k ∈ R5 v ∪ Tr, slotHit Hb p₁ (G.σ₁ v.s) v.o₁ v.u.2 k := by
      obtain ⟨k, hk, hx⟩ := h
      refine ⟨k, hk, ?_⟩
      rw [hy', ho]
      exact slotHit_of y _ _ k hx
    rcases hit_others h' hT with h | h
    · rcases h with h | h | h
      · exact Or.inl (Or.inr (Or.inl h))
      · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
    · exact Or.inr (Or.inl (Or.inr h))

set_option maxRecDepth 8000 in
lemma bad₂ (hm : MainP p₂) (R5 : GView S p₁ p₂ p₃ p₄ → Finset (Bytes 37))
    (v : GView S p₁ p₂ p₃ p₄) (y : SW) (c : SimCoins p₂) (Tr : Finset (Bytes 37))
    (hy' : G.σ₂ v.s v.o₁ = some y) (ho : v.o₂ = some (simulate p₂ c))
    (hT : ∀ k ∈ Tr, slotErr v.o₁ ∨ slotErr v.o₃ ∨ slotErr v.o₄ ∨
      k ∈ slotKeys Hb p₁ (yv₁ G v) v.o₁ v.u.2 ∪ slotKeys Hb p₃ (yv₃ G v) v.o₃ v.u.2 ∪
        slotKeys Hb p₄ (yv₄ G v) v.o₄ v.u.2)
    (hz : (letI : HasPrg := icPrg v.u.2
      wPre y.2 ∈ candidatesG Hb CrtGen.tables (withP y.1 p₂) enc5 hm (R5 v ∪ Tr) c.1 c.2)) :
    bstar Hb G R5 v := by
  show bstarCore Hb G v.s v.o₁ v.o₂ v.o₃ v.o₄ v.u.2 (R5 v)
  rcases @pred_imp Hb (icPrg v.u.2) p₂ hm y c _ hz with h | h | h
  · exact Or.inl (Or.inr (Or.inl (ho ▸ h)))
  · refine Or.inr (Or.inr (Or.inl (Or.inl ?_)))
    rw [hy', ho]; exact h
  · have h' : ∃ k ∈ R5 v ∪ Tr, slotHit Hb p₂ (G.σ₂ v.s v.o₁) v.o₂ v.u.2 k := by
      obtain ⟨k, hk, hx⟩ := h
      refine ⟨k, hk, ?_⟩
      rw [hy', ho]
      exact slotHit_of y _ _ k hx
    rcases hit_others h' hT with h | h
    · rcases h with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
    · exact Or.inr (Or.inr (Or.inl (Or.inr h)))

set_option maxRecDepth 8000 in
lemma bad₃ (hm : MainP p₃) (R5 : GView S p₁ p₂ p₃ p₄ → Finset (Bytes 37))
    (v : GView S p₁ p₂ p₃ p₄) (y : SW) (c : SimCoins p₃) (Tr : Finset (Bytes 37))
    (hy' : G.σ₃ v.s v.o₁ v.o₂ = some y) (ho : v.o₃ = some (simulate p₃ c))
    (hT : ∀ k ∈ Tr, slotErr v.o₁ ∨ slotErr v.o₂ ∨ slotErr v.o₄ ∨
      k ∈ slotKeys Hb p₁ (yv₁ G v) v.o₁ v.u.2 ∪ slotKeys Hb p₂ (yv₂ G v) v.o₂ v.u.2 ∪
        slotKeys Hb p₄ (yv₄ G v) v.o₄ v.u.2)
    (hz : (letI : HasPrg := icPrg v.u.2
      wPre y.2 ∈ candidatesG Hb CrtGen.tables (withP y.1 p₃) enc5 hm (R5 v ∪ Tr) c.1 c.2)) :
    bstar Hb G R5 v := by
  show bstarCore Hb G v.s v.o₁ v.o₂ v.o₃ v.o₄ v.u.2 (R5 v)
  rcases @pred_imp Hb (icPrg v.u.2) p₃ hm y c _ hz with h | h | h
  · exact Or.inl (Or.inr (Or.inr (Or.inl (ho ▸ h))))
  · refine Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ?_))))
    rw [hy', ho]; exact h
  · have h' : ∃ k ∈ R5 v ∪ Tr, slotHit Hb p₃ (G.σ₃ v.s v.o₁ v.o₂) v.o₃ v.u.2 k := by
      obtain ⟨k, hk, hx⟩ := h
      refine ⟨k, hk, ?_⟩
      rw [hy', ho]
      exact slotHit_of y _ _ k hx
    rcases hit_others h' hT with h | h
    · rcases h with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr (Or.inl h))
      · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr h))))

set_option maxRecDepth 8000 in
lemma bad₄ (hm : MainP p₄) (R5 : GView S p₁ p₂ p₃ p₄ → Finset (Bytes 37))
    (v : GView S p₁ p₂ p₃ p₄) (y : SW) (c : SimCoins p₄) (Tr : Finset (Bytes 37))
    (hy' : G.σ₄ v.s v.o₁ v.o₂ v.o₃ = some y) (ho : v.o₄ = some (simulate p₄ c))
    (hT : ∀ k ∈ Tr, slotErr v.o₁ ∨ slotErr v.o₂ ∨ slotErr v.o₃ ∨
      k ∈ slotKeys Hb p₁ (yv₁ G v) v.o₁ v.u.2 ∪ slotKeys Hb p₂ (yv₂ G v) v.o₂ v.u.2 ∪
        slotKeys Hb p₃ (yv₃ G v) v.o₃ v.u.2)
    (hz : (letI : HasPrg := icPrg v.u.2
      wPre y.2 ∈ candidatesG Hb CrtGen.tables (withP y.1 p₄) enc5 hm (R5 v ∪ Tr) c.1 c.2)) :
    bstar Hb G R5 v := by
  show bstarCore Hb G v.s v.o₁ v.o₂ v.o₃ v.o₄ v.u.2 (R5 v)
  rcases @pred_imp Hb (icPrg v.u.2) p₄ hm y c _ hz with h | h | h
  · exact Or.inl (Or.inr (Or.inr (Or.inr (ho ▸ h))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
    rw [hy', ho]; exact h
  · have h' : ∃ k ∈ R5 v ∪ Tr, slotHit Hb p₄ (G.σ₄ v.s v.o₁ v.o₂ v.o₃) v.o₄ v.u.2 k := by
      obtain ⟨k, hk, hx⟩ := h
      refine ⟨k, hk, ?_⟩
      rw [hy', ho]
      exact slotHit_of y _ _ k hx
    rcases hit_others h' hT with h | h
    · rcases h with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr (Or.inl h))
      · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

end Bad


/-! ## The four hops -/

section Hops

variable {S : Type} {p₀ : Params} {n₁ n₂ n₃ n₄ : ℕ} (Hb : Hashes) (G : Game S Out SW SW SW SW)

set_option maxRecDepth 8000 in
/-- **Replacing proof 1** on the shared tables (the earlier outputs do not depend on the tables;
the earlier programmings change only blocks with tails in `T`). -/
theorem hop23₁ (hm : MainP (pw p₀ n₁)) (hp : SmallParams (pw p₀ n₁)) (hHb : HashesWF Hb)
    (hv : GValid G (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄))
    (Ψ : GView S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) → Prop)
    (R5 : GView S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) → Finset (Bytes 37)) {q3 qE : ℕ}
    (hΨ : Rd Ψ R5 q3 qE) (s : S) (b₂ : SB (pw p₀ n₂)) (b₃ : SB (pw p₀ n₃)) (b₄ : SB (pw p₀ n₄))
    (k₂ : b₂.OK) (k₃ : b₃.OK) (k₄ : b₄.OK) (c₂ : b₂.Cov Hb) (c₃ : b₃.Cov Hb) (c₄ : b₄.Cov Hb) (i₂ : ∀ y u, b₂.pg y u = id) (i₃ : ∀ y u, b₃.pg y u = id) (i₄ : ∀ y u, b₄.pg y u = id) :
    |pr (USh × KS (pw p₀ n₁)) (fun z => Ψ (viewOf23 G s z.2.2.2 z.1 (realSB Hb _ z.2.1.1 z.2.2.1) b₂ b₃ b₄)) -
      pr (USh × KS (pw p₀ n₁)) (fun z => Ψ (viewOf23 G s z.2.2.2 z.1 (simSB Hb _ z.2.1.2 z.2.2.1) b₂ b₃ b₄))| ≤
      εS q3 (qE + 4 * 4607) + Δ23 p₀.qsDegree + pr (USh × KS (pw p₀ n₁)) (fun z =>
        bstar Hb G R5 (viewOf23 G s z.2.2.2 z.1 (simSB Hb _ z.2.1.2 z.2.2.1) b₂ b₃ b₄)) := by
  classical
  have hΔ := Δ23_nonneg p₀.qsDegree
  rcases hy : G.σ₁ s with _ | y
  · have e : ∀ z : USh × KS (pw p₀ n₁), viewOf23 G s z.2.2.2 z.1 (simSB Hb _ z.2.1.2 z.2.2.1) b₂ b₃ b₄ = viewOf23 G s z.2.2.2 z.1 (realSB Hb _ z.2.1.1 z.2.2.1) b₂ b₃ b₄ := by
      intro z
      simp only [viewOf23, hy, i₂, i₃, i₄]
      rfl
    have e' : (fun z : USh × KS (pw p₀ n₁) => Ψ (viewOf23 G s z.2.2.2 z.1 (simSB Hb _ z.2.1.2 z.2.2.1) b₂ b₃ b₄)) =
        fun z => Ψ (viewOf23 G s z.2.2.2 z.1 (realSB Hb _ z.2.1.1 z.2.2.1) b₂ b₃ b₄) := funext fun z => by rw [e z]
    rw [e', sub_self, abs_zero]
    have := εS_nonneg q3 (qE + 4 * 4607)
    have := pr_nonneg (α := USh × KS (pw p₀ n₁)) (fun z => bstar Hb G R5 (viewOf23 G s z.2.2.2 z.1 (simSB Hb _ z.2.1.2 z.2.2.1) b₂ b₃ b₄))
    linarith
  · let C : Out → VP (pw p₀ n₁) → USh → GView S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) :=
      fun o V u => viewOf23 G s V.2 u (givenSB (pw p₀ n₁) o V.1) b₂ b₃ b₄
    have eR : ∀ z : USh × KS (pw p₀ n₁), viewOf23 G s z.2.2.2 z.1 (realSB Hb _ z.2.1.1 z.2.2.1) b₂ b₃ b₄ =
        C (realRO (pw p₀ n₁) Hb (withP y.1 (pw p₀ n₁)) y.2 z.2.1.1 z.2.2.1 (shOf z.2.2.2 z.1)) z.2.2 z.1 := by
      intro z
      simp only [C, viewOf23, hy, Option.map_some, i₂, i₃, i₄]
      rfl
    have eS : ∀ z : USh × KS (pw p₀ n₁), viewOf23 G s z.2.2.2 z.1 (simSB Hb _ z.2.1.2 z.2.2.1) b₂ b₃ b₄ =
        C (simulate (pw p₀ n₁) z.2.1.2)
          (z.2.2.1, (progRO (pw p₀ n₁) Hb (withP y.1 (pw p₀ n₁)) z.2.1.2 (shOf z.2.2.2 z.1)).1) z.1 := by
      intro z
      simp only [C, viewOf23, hy, Option.map_some, i₂, i₃, i₄]
      rfl
    have key := ctx_hop Hb hm hp hHb y (hv.v₁ s y hy) Ψ R5 C
      (fun o V u => tr5 G s V.2 u (givenSB (pw p₀ n₁) o V.1) b₂ b₃ b₄)
      (fun o V u => trE G s V.2 u (givenSB (pw p₀ n₁) o V.1) b₂ b₃ b₄) (fun _ _ _ => rfl)
      (fun o V u G5 h => viewOf23_G5 G s V.2 u (givenSB_ok o V.1) k₂ k₃ k₄ G5 h)
      (fun o V u E h => viewOf23_E G s V.2 u (givenSB_ok o V.1) k₂ k₃ k₄ E h)
      (fun o V u => card_trE G (givenSB_ok o V.1) k₂ k₃ k₄ s V.2 u)
      GView.with3₁ (fun v => v.v₁.1) (fun o G3 G3' G2 u => ⟨rfl, rfl⟩) hΨ.h5 hΨ.hE hΨ.h3₁
    have hbad : pr (USh × KS (pw p₀ n₁)) (fun z => mainPredIC Hb (withP y.1 (pw p₀ n₁)) hm
        (fun o G3 G2 G5 E => R5 (C o (G3, G2) (G5, E)) ∪
          tr5 G s G2 (G5, E) (givenSB (pw p₀ n₁) o G3) b₂ b₃ b₄) (wPre y.2)
        ((z.2.1.2, (z.2.2.1, z.2.2.2, z.1.1)), z.1.2)) ≤
        pr (USh × KS (pw p₀ n₁)) (fun z => bstar Hb G R5 (viewOf23 G s z.2.2.2 z.1 (simSB Hb _ z.2.1.2 z.2.2.1) b₂ b₃ b₄)) := by
      refine pr_mono fun z hz => ?_
      rw [eS z, progRO_fst Hb (withP y.1 (pw p₀ n₁)) z.2.1.2 (shOf z.2.2.2 z.1)]
      unfold mainPredIC mainPred2 at hz
      refine bad₁ Hb G hm R5 _ y z.2.1.2 _ ?_ ?_ ?_ hz

      · simp only [C, viewOf23]
        exact hy
      · simp only [C, viewOf23, hy, i₂, i₃, i₄]
        rfl
      · intro k hk
        dsimp only [tr5] at hk
        rcases mem_union.1 hk with hk | h₄
        · rcases mem_union.1 hk with hk | h₃
          · rcases mem_union.1 hk with h₁ | h₂
            · simp [givenSB] at h₁
            · rcases cov23 Hb k₂ c₂ _ (hv.v₂ _ _) _ h₂ with h | h
              · exact Or.inl h
              · exact Or.inr (Or.inr (Or.inr (mem_union_left _ (mem_union_left _ h))))
          · rcases cov23 Hb k₃ c₃ _ (hv.v₃ _ _ _) _ h₃ with h | h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inr (mem_union_left _ (mem_union_right _ h))))
        · rcases cov23 Hb k₄ c₄ _ (hv.v₄ _ _ _ _) _ h₄ with h | h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr (mem_union_right _ h)))
    simp only [eR, eS] at key ⊢
    simp only [eS] at hbad
    linarith

set_option maxRecDepth 8000 in
/-- **Replacing proof 2** on the shared tables (the earlier outputs do not depend on the tables;
the earlier programmings change only blocks with tails in `T`). -/
theorem hop23₂ (hm : MainP (pw p₀ n₂)) (hp : SmallParams (pw p₀ n₂)) (hHb : HashesWF Hb)
    (hv : GValid G (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄))
    (Ψ : GView S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) → Prop)
    (R5 : GView S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) → Finset (Bytes 37)) {q3 qE : ℕ}
    (hΨ : Rd Ψ R5 q3 qE) (s : S) (b₁ : SB (pw p₀ n₁)) (b₃ : SB (pw p₀ n₃)) (b₄ : SB (pw p₀ n₄))
    (k₁ : b₁.OK) (k₃ : b₃.OK) (k₄ : b₄.OK) (c₁ : b₁.Cov Hb) (c₃ : b₃.Cov Hb) (c₄ : b₄.Cov Hb) (oa : Option Out) (ho₁ : ∀ t, (G.σ₁ s).map (b₁.run · t) = oa) (T₁ : Finset ByteArray) (hT₁ : T₁.card ≤ 1) (l₁ : b₁.Tl T₁) (i₃ : ∀ y u, b₃.pg y u = id) (i₄ : ∀ y u, b₄.pg y u = id) :
    |pr (USh × KS (pw p₀ n₂)) (fun z => Ψ (viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ (realSB Hb _ z.2.1.1 z.2.2.1) b₃ b₄)) -
      pr (USh × KS (pw p₀ n₂)) (fun z => Ψ (viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ (simSB Hb _ z.2.1.2 z.2.2.1) b₃ b₄))| ≤
      εS q3 (qE + 4 * 4607) + Δ23 p₀.qsDegree + pr (USh × KS (pw p₀ n₂)) (fun z =>
        bstar Hb G R5 (viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ (simSB Hb _ z.2.1.2 z.2.2.1) b₃ b₄)) := by
  classical
  have hΔ := Δ23_nonneg p₀.qsDegree
  rcases hy : G.σ₂ s oa with _ | y
  · have e : ∀ z : USh × KS (pw p₀ n₂), viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ (simSB Hb _ z.2.1.2 z.2.2.1) b₃ b₄ = viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ (realSB Hb _ z.2.1.1 z.2.2.1) b₃ b₄ := by
      intro z
      simp only [viewOf23, ho₁, hy, i₃, i₄]
      rfl
    have e' : (fun z : USh × KS (pw p₀ n₂) => Ψ (viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ (simSB Hb _ z.2.1.2 z.2.2.1) b₃ b₄)) =
        fun z => Ψ (viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ (realSB Hb _ z.2.1.1 z.2.2.1) b₃ b₄) := funext fun z => by rw [e z]
    rw [e', sub_self, abs_zero]
    have := εS_nonneg q3 (qE + 4 * 4607)
    have := pr_nonneg (α := USh × KS (pw p₀ n₂)) (fun z => bstar Hb G R5 (viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ (simSB Hb _ z.2.1.2 z.2.2.1) b₃ b₄))
    linarith
  · let C : Out → VP (pw p₀ n₂) → USh → GView S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) :=
      fun o V u => viewOf23 (n₁ := n₁) G s V.2 u b₁ (givenSB (pw p₀ n₂) o V.1) b₃ b₄
    have eR : ∀ z : USh × KS (pw p₀ n₂), viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ (realSB Hb _ z.2.1.1 z.2.2.1) b₃ b₄ =
        C (realRO (pw p₀ n₂) Hb (withP y.1 (pw p₀ n₂)) y.2 z.2.1.1 z.2.2.1 (((fun u G2 => b₁.pg (G.σ₁ s) u (G2)) z.1 z.2.2.2, z.1) : Sh (pw p₀ n₂)))
          z.2.2 z.1 := by
      intro z
      simp only [C, viewOf23, ho₁, hy, Option.map_some, i₃, i₄]
      rfl
    have eS : ∀ z : USh × KS (pw p₀ n₂), viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ (simSB Hb _ z.2.1.2 z.2.2.1) b₃ b₄ =
        C (simulate (pw p₀ n₂) z.2.1.2)
          (z.2.2.1, (progRO (pw p₀ n₂) Hb (withP y.1 (pw p₀ n₂)) z.2.1.2 (shOf z.2.2.2 z.1)).1) z.1 := by
      intro z
      simp only [C, viewOf23, ho₁, hy, Option.map_some, i₃, i₄]
      rfl
    have key := ctx_hop Hb hm hp hHb y (hv.v₂ s oa y hy) Ψ R5 C
      (fun o V u => tr5 (n₁ := n₁) G s V.2 u b₁ (givenSB (pw p₀ n₂) o V.1) b₃ b₄)
      (fun o V u => trE (n₁ := n₁) G s V.2 u b₁ (givenSB (pw p₀ n₂) o V.1) b₃ b₄) (fun _ _ _ => rfl)
      (fun o V u G5 h => viewOf23_G5 (n₁ := n₁) G s V.2 u k₁ (givenSB_ok o V.1) k₃ k₄ G5 h)
      (fun o V u E h => viewOf23_E (n₁ := n₁) G s V.2 u k₁ (givenSB_ok o V.1) k₃ k₄ E h)
      (fun o V u => card_trE G k₁ (givenSB_ok o V.1) k₃ k₄ s V.2 u)
      GView.with3₂ (fun v => v.v₂.1) (fun o G3 G3' G2 u => ⟨rfl, rfl⟩) hΨ.h5 hΨ.hE hΨ.h3₂
    have hbad : pr (USh × KS (pw p₀ n₂)) (fun z => mainPredIC Hb (withP y.1 (pw p₀ n₂)) hm
        (fun o G3 G2 G5 E => R5 (C o (G3, G2) (G5, E)) ∪
          tr5 (n₁ := n₁) G s G2 (G5, E) b₁ (givenSB (pw p₀ n₂) o G3) b₃ b₄) (wPre y.2)
        ((z.2.1.2, (z.2.2.1, z.2.2.2, z.1.1)), z.1.2)) ≤
        pr (USh × KS (pw p₀ n₂)) (fun z => bstar Hb G R5 (viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ (simSB Hb _ z.2.1.2 z.2.2.1) b₃ b₄)) := by
      refine pr_mono fun z hz => ?_
      rw [eS z, progRO_fst Hb (withP y.1 (pw p₀ n₂)) z.2.1.2 (shOf z.2.2.2 z.1)]
      unfold mainPredIC mainPred2 at hz
      refine bad₂ Hb G hm R5 _ y z.2.1.2 _ ?_ ?_ ?_ hz

      · simp only [C, viewOf23, ho₁]
        exact hy
      · simp only [C, viewOf23, ho₁, hy, i₃, i₄]
        rfl
      · intro k hk
        dsimp only [tr5] at hk
        rcases mem_union.1 hk with hk | h₄
        · rcases mem_union.1 hk with hk | h₃
          · rcases mem_union.1 hk with h₁ | h₂
            · rcases cov23 Hb k₁ c₁ _ (hv.v₁ _) _ h₁ with h | h
              · exact Or.inl h
              · exact Or.inr (Or.inr (Or.inr (mem_union_left _ (mem_union_left _ h))))
            · simp [givenSB] at h₂
          · rcases cov23 Hb k₃ c₃ _ (hv.v₃ _ _ _) _ h₃ with h | h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inr (mem_union_left _ (mem_union_right _ h))))
        · rcases cov23 Hb k₄ c₄ _ (hv.v₄ _ _ _ _) _ h₄ with h | h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr (mem_union_right _ h)))
    have hδ : |pr (USh × KS (pw p₀ n₂)) (fun z => Ψ (viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ (realSB Hb _ z.2.1.1 z.2.2.1) b₃ b₄)) -
        pr (USh × KS (pw p₀ n₂)) (fun z => Ψ (C (realRO (pw p₀ n₂) Hb (withP y.1 (pw p₀ n₂)) y.2 z.2.1.1 z.2.2.1
          (shOf z.2.2.2 z.1)) z.2.2 z.1))| ≤ Δ23 p₀.qsDegree := by
      refine (abs_pr_sub_le_of_agree _ _ _ fun z hz => ?_).trans
        (pr_collide_slot Hb hm hp hHb y (hv.v₂ s oa y hy) (fun u G2 => b₁.pg (G.σ₁ s) u (G2)) (T₁) ?_ ?_)
      · rw [eR z, not_not.1 hz]
      · exact hT₁.trans (by norm_num)
      · intro u G2 k hk
        exact l₁ _ _ _ k hk
    simp only [eS] at key hbad ⊢
    have := abs_sub_le (pr (USh × KS (pw p₀ n₂)) (fun z => Ψ (viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ (realSB Hb _ z.2.1.1 z.2.2.1) b₃ b₄)))
      (pr (USh × KS (pw p₀ n₂)) (fun z => Ψ (C (realRO (pw p₀ n₂) Hb (withP y.1 (pw p₀ n₂)) y.2 z.2.1.1 z.2.2.1
          (shOf z.2.2.2 z.1)) z.2.2 z.1)))
      (pr (USh × KS (pw p₀ n₂)) (fun z => Ψ (C (simulate (pw p₀ n₂) z.2.1.2)
          (z.2.2.1, (progRO (pw p₀ n₂) Hb (withP y.1 (pw p₀ n₂)) z.2.1.2 (shOf z.2.2.2 z.1)).1) z.1)))
    linarith

set_option maxRecDepth 8000 in
/-- **Replacing proof 3** on the shared tables (the earlier outputs do not depend on the tables;
the earlier programmings change only blocks with tails in `T`). -/
theorem hop23₃ (hm : MainP (pw p₀ n₃)) (hp : SmallParams (pw p₀ n₃)) (hHb : HashesWF Hb)
    (hv : GValid G (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄))
    (Ψ : GView S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) → Prop)
    (R5 : GView S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) → Finset (Bytes 37)) {q3 qE : ℕ}
    (hΨ : Rd Ψ R5 q3 qE) (s : S) (b₁ : SB (pw p₀ n₁)) (b₂ : SB (pw p₀ n₂)) (b₄ : SB (pw p₀ n₄))
    (k₁ : b₁.OK) (k₂ : b₂.OK) (k₄ : b₄.OK) (c₁ : b₁.Cov Hb) (c₂ : b₂.Cov Hb) (c₄ : b₄.Cov Hb) (oa : Option Out) (ho₁ : ∀ t, (G.σ₁ s).map (b₁.run · t) = oa) (T₁ : Finset ByteArray) (hT₁ : T₁.card ≤ 1) (l₁ : b₁.Tl T₁) (ob : Option Out) (ho₂ : ∀ t, (G.σ₂ s oa).map (b₂.run · t) = ob) (T₂ : Finset ByteArray) (hT₂ : T₂.card ≤ 1) (l₂ : b₂.Tl T₂) (i₄ : ∀ y u, b₄.pg y u = id) :
    |pr (USh × KS (pw p₀ n₃)) (fun z => Ψ (viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ b₂ (realSB Hb _ z.2.1.1 z.2.2.1) b₄)) -
      pr (USh × KS (pw p₀ n₃)) (fun z => Ψ (viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ b₂ (simSB Hb _ z.2.1.2 z.2.2.1) b₄))| ≤
      εS q3 (qE + 4 * 4607) + Δ23 p₀.qsDegree + pr (USh × KS (pw p₀ n₃)) (fun z =>
        bstar Hb G R5 (viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ b₂ (simSB Hb _ z.2.1.2 z.2.2.1) b₄)) := by
  classical
  have hΔ := Δ23_nonneg p₀.qsDegree
  rcases hy : G.σ₃ s oa ob with _ | y
  · have e : ∀ z : USh × KS (pw p₀ n₃), viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ b₂ (simSB Hb _ z.2.1.2 z.2.2.1) b₄ = viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ b₂ (realSB Hb _ z.2.1.1 z.2.2.1) b₄ := by
      intro z
      simp only [viewOf23, ho₁, ho₂, hy, i₄]
      rfl
    have e' : (fun z : USh × KS (pw p₀ n₃) => Ψ (viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ b₂ (simSB Hb _ z.2.1.2 z.2.2.1) b₄)) =
        fun z => Ψ (viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ b₂ (realSB Hb _ z.2.1.1 z.2.2.1) b₄) := funext fun z => by rw [e z]
    rw [e', sub_self, abs_zero]
    have := εS_nonneg q3 (qE + 4 * 4607)
    have := pr_nonneg (α := USh × KS (pw p₀ n₃)) (fun z => bstar Hb G R5 (viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ b₂ (simSB Hb _ z.2.1.2 z.2.2.1) b₄))
    linarith
  · let C : Out → VP (pw p₀ n₃) → USh → GView S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) :=
      fun o V u => viewOf23 (n₁ := n₁) G s V.2 u b₁ b₂ (givenSB (pw p₀ n₃) o V.1) b₄
    have eR : ∀ z : USh × KS (pw p₀ n₃), viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ b₂ (realSB Hb _ z.2.1.1 z.2.2.1) b₄ =
        C (realRO (pw p₀ n₃) Hb (withP y.1 (pw p₀ n₃)) y.2 z.2.1.1 z.2.2.1 (((fun u G2 => b₁.pg (G.σ₁ s) u (b₂.pg (G.σ₂ s oa) u (G2))) z.1 z.2.2.2, z.1) : Sh (pw p₀ n₃)))
          z.2.2 z.1 := by
      intro z
      simp only [C, viewOf23, ho₁, ho₂, hy, Option.map_some, i₄]
      rfl
    have eS : ∀ z : USh × KS (pw p₀ n₃), viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ b₂ (simSB Hb _ z.2.1.2 z.2.2.1) b₄ =
        C (simulate (pw p₀ n₃) z.2.1.2)
          (z.2.2.1, (progRO (pw p₀ n₃) Hb (withP y.1 (pw p₀ n₃)) z.2.1.2 (shOf z.2.2.2 z.1)).1) z.1 := by
      intro z
      simp only [C, viewOf23, ho₁, ho₂, hy, Option.map_some, i₄]
      rfl
    have key := ctx_hop Hb hm hp hHb y (hv.v₃ s oa ob y hy) Ψ R5 C
      (fun o V u => tr5 (n₁ := n₁) G s V.2 u b₁ b₂ (givenSB (pw p₀ n₃) o V.1) b₄)
      (fun o V u => trE (n₁ := n₁) G s V.2 u b₁ b₂ (givenSB (pw p₀ n₃) o V.1) b₄) (fun _ _ _ => rfl)
      (fun o V u G5 h => viewOf23_G5 (n₁ := n₁) G s V.2 u k₁ k₂ (givenSB_ok o V.1) k₄ G5 h)
      (fun o V u E h => viewOf23_E (n₁ := n₁) G s V.2 u k₁ k₂ (givenSB_ok o V.1) k₄ E h)
      (fun o V u => card_trE G k₁ k₂ (givenSB_ok o V.1) k₄ s V.2 u)
      GView.with3₃ (fun v => v.v₃.1) (fun o G3 G3' G2 u => ⟨rfl, rfl⟩) hΨ.h5 hΨ.hE hΨ.h3₃
    have hbad : pr (USh × KS (pw p₀ n₃)) (fun z => mainPredIC Hb (withP y.1 (pw p₀ n₃)) hm
        (fun o G3 G2 G5 E => R5 (C o (G3, G2) (G5, E)) ∪
          tr5 (n₁ := n₁) G s G2 (G5, E) b₁ b₂ (givenSB (pw p₀ n₃) o G3) b₄) (wPre y.2)
        ((z.2.1.2, (z.2.2.1, z.2.2.2, z.1.1)), z.1.2)) ≤
        pr (USh × KS (pw p₀ n₃)) (fun z => bstar Hb G R5 (viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ b₂ (simSB Hb _ z.2.1.2 z.2.2.1) b₄)) := by
      refine pr_mono fun z hz => ?_
      rw [eS z, progRO_fst Hb (withP y.1 (pw p₀ n₃)) z.2.1.2 (shOf z.2.2.2 z.1)]
      unfold mainPredIC mainPred2 at hz
      refine bad₃ Hb G hm R5 _ y z.2.1.2 _ ?_ ?_ ?_ hz

      · simp only [C, viewOf23, ho₁, ho₂]
        exact hy
      · simp only [C, viewOf23, ho₁, ho₂, hy, i₄]
        rfl
      · intro k hk
        dsimp only [tr5] at hk
        rcases mem_union.1 hk with hk | h₄
        · rcases mem_union.1 hk with hk | h₃
          · rcases mem_union.1 hk with h₁ | h₂
            · rcases cov23 Hb k₁ c₁ _ (hv.v₁ _) _ h₁ with h | h
              · exact Or.inl h
              · exact Or.inr (Or.inr (Or.inr (mem_union_left _ (mem_union_left _ h))))
            · rcases cov23 Hb k₂ c₂ _ (hv.v₂ _ _) _ h₂ with h | h
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr (Or.inr (mem_union_left _ (mem_union_right _ h))))
          · simp [givenSB] at h₃
        · rcases cov23 Hb k₄ c₄ _ (hv.v₄ _ _ _ _) _ h₄ with h | h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr (mem_union_right _ h)))
    have hδ : |pr (USh × KS (pw p₀ n₃)) (fun z => Ψ (viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ b₂ (realSB Hb _ z.2.1.1 z.2.2.1) b₄)) -
        pr (USh × KS (pw p₀ n₃)) (fun z => Ψ (C (realRO (pw p₀ n₃) Hb (withP y.1 (pw p₀ n₃)) y.2 z.2.1.1 z.2.2.1
          (shOf z.2.2.2 z.1)) z.2.2 z.1))| ≤ Δ23 p₀.qsDegree := by
      refine (abs_pr_sub_le_of_agree _ _ _ fun z hz => ?_).trans
        (pr_collide_slot Hb hm hp hHb y (hv.v₃ s oa ob y hy) (fun u G2 => b₁.pg (G.σ₁ s) u (b₂.pg (G.σ₂ s oa) u (G2))) (T₁ ∪ T₂) ?_ ?_)
      · rw [eR z, not_not.1 hz]
      · exact (card_union_le _ _).trans (by omega)
      · intro u G2 k hk
        simp only [mem_union, not_or] at hk
        exact (l₁ _ _ _ k hk.1).trans (l₂ _ _ _ k hk.2)
    simp only [eS] at key hbad ⊢
    have := abs_sub_le (pr (USh × KS (pw p₀ n₃)) (fun z => Ψ (viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ b₂ (realSB Hb _ z.2.1.1 z.2.2.1) b₄)))
      (pr (USh × KS (pw p₀ n₃)) (fun z => Ψ (C (realRO (pw p₀ n₃) Hb (withP y.1 (pw p₀ n₃)) y.2 z.2.1.1 z.2.2.1
          (shOf z.2.2.2 z.1)) z.2.2 z.1)))
      (pr (USh × KS (pw p₀ n₃)) (fun z => Ψ (C (simulate (pw p₀ n₃) z.2.1.2)
          (z.2.2.1, (progRO (pw p₀ n₃) Hb (withP y.1 (pw p₀ n₃)) z.2.1.2 (shOf z.2.2.2 z.1)).1) z.1)))
    linarith

set_option maxRecDepth 8000 in
/-- **Replacing proof 4** on the shared tables (the earlier outputs do not depend on the tables;
the earlier programmings change only blocks with tails in `T`). -/
theorem hop23₄ (hm : MainP (pw p₀ n₄)) (hp : SmallParams (pw p₀ n₄)) (hHb : HashesWF Hb)
    (hv : GValid G (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄))
    (Ψ : GView S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) → Prop)
    (R5 : GView S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) → Finset (Bytes 37)) {q3 qE : ℕ}
    (hΨ : Rd Ψ R5 q3 qE) (s : S) (b₁ : SB (pw p₀ n₁)) (b₂ : SB (pw p₀ n₂)) (b₃ : SB (pw p₀ n₃))
    (k₁ : b₁.OK) (k₂ : b₂.OK) (k₃ : b₃.OK) (c₁ : b₁.Cov Hb) (c₂ : b₂.Cov Hb) (c₃ : b₃.Cov Hb) (oa : Option Out) (ho₁ : ∀ t, (G.σ₁ s).map (b₁.run · t) = oa) (T₁ : Finset ByteArray) (hT₁ : T₁.card ≤ 1) (l₁ : b₁.Tl T₁) (ob : Option Out) (ho₂ : ∀ t, (G.σ₂ s oa).map (b₂.run · t) = ob) (T₂ : Finset ByteArray) (hT₂ : T₂.card ≤ 1) (l₂ : b₂.Tl T₂) (oc : Option Out) (ho₃ : ∀ t, (G.σ₃ s oa ob).map (b₃.run · t) = oc) (T₃ : Finset ByteArray) (hT₃ : T₃.card ≤ 1) (l₃ : b₃.Tl T₃) :
    |pr (USh × KS (pw p₀ n₄)) (fun z => Ψ (viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ b₂ b₃ (realSB Hb _ z.2.1.1 z.2.2.1))) -
      pr (USh × KS (pw p₀ n₄)) (fun z => Ψ (viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ b₂ b₃ (simSB Hb _ z.2.1.2 z.2.2.1)))| ≤
      εS q3 (qE + 4 * 4607) + Δ23 p₀.qsDegree + pr (USh × KS (pw p₀ n₄)) (fun z =>
        bstar Hb G R5 (viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ b₂ b₃ (simSB Hb _ z.2.1.2 z.2.2.1))) := by
  classical
  have hΔ := Δ23_nonneg p₀.qsDegree
  rcases hy : G.σ₄ s oa ob oc with _ | y
  · have e : ∀ z : USh × KS (pw p₀ n₄), viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ b₂ b₃ (simSB Hb _ z.2.1.2 z.2.2.1) = viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ b₂ b₃ (realSB Hb _ z.2.1.1 z.2.2.1) := by
      intro z
      simp only [viewOf23, ho₁, ho₂, ho₃, hy]
      rfl
    have e' : (fun z : USh × KS (pw p₀ n₄) => Ψ (viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ b₂ b₃ (simSB Hb _ z.2.1.2 z.2.2.1))) =
        fun z => Ψ (viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ b₂ b₃ (realSB Hb _ z.2.1.1 z.2.2.1)) := funext fun z => by rw [e z]
    rw [e', sub_self, abs_zero]
    have := εS_nonneg q3 (qE + 4 * 4607)
    have := pr_nonneg (α := USh × KS (pw p₀ n₄)) (fun z => bstar Hb G R5 (viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ b₂ b₃ (simSB Hb _ z.2.1.2 z.2.2.1)))
    linarith
  · let C : Out → VP (pw p₀ n₄) → USh → GView S (pw p₀ n₁) (pw p₀ n₂) (pw p₀ n₃) (pw p₀ n₄) :=
      fun o V u => viewOf23 (n₁ := n₁) G s V.2 u b₁ b₂ b₃ (givenSB (pw p₀ n₄) o V.1)
    have eR : ∀ z : USh × KS (pw p₀ n₄), viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ b₂ b₃ (realSB Hb _ z.2.1.1 z.2.2.1) =
        C (realRO (pw p₀ n₄) Hb (withP y.1 (pw p₀ n₄)) y.2 z.2.1.1 z.2.2.1 (((fun u G2 => b₁.pg (G.σ₁ s) u (b₂.pg (G.σ₂ s oa) u (b₃.pg (G.σ₃ s oa ob) u (G2)))) z.1 z.2.2.2, z.1) : Sh (pw p₀ n₄)))
          z.2.2 z.1 := by
      intro z
      simp only [C, viewOf23, ho₁, ho₂, ho₃, hy, Option.map_some]
      rfl
    have eS : ∀ z : USh × KS (pw p₀ n₄), viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ b₂ b₃ (simSB Hb _ z.2.1.2 z.2.2.1) =
        C (simulate (pw p₀ n₄) z.2.1.2)
          (z.2.2.1, (progRO (pw p₀ n₄) Hb (withP y.1 (pw p₀ n₄)) z.2.1.2 (shOf z.2.2.2 z.1)).1) z.1 := by
      intro z
      simp only [C, viewOf23, ho₁, ho₂, ho₃, hy, Option.map_some]
      rfl
    have key := ctx_hop Hb hm hp hHb y (hv.v₄ s oa ob oc y hy) Ψ R5 C
      (fun o V u => tr5 (n₁ := n₁) G s V.2 u b₁ b₂ b₃ (givenSB (pw p₀ n₄) o V.1))
      (fun o V u => trE (n₁ := n₁) G s V.2 u b₁ b₂ b₃ (givenSB (pw p₀ n₄) o V.1)) (fun _ _ _ => rfl)
      (fun o V u G5 h => viewOf23_G5 (n₁ := n₁) G s V.2 u k₁ k₂ k₃ (givenSB_ok o V.1) G5 h)
      (fun o V u E h => viewOf23_E (n₁ := n₁) G s V.2 u k₁ k₂ k₃ (givenSB_ok o V.1) E h)
      (fun o V u => card_trE G k₁ k₂ k₃ (givenSB_ok o V.1) s V.2 u)
      GView.with3₄ (fun v => v.v₄.1) (fun o G3 G3' G2 u => ⟨rfl, rfl⟩) hΨ.h5 hΨ.hE hΨ.h3₄
    have hbad : pr (USh × KS (pw p₀ n₄)) (fun z => mainPredIC Hb (withP y.1 (pw p₀ n₄)) hm
        (fun o G3 G2 G5 E => R5 (C o (G3, G2) (G5, E)) ∪
          tr5 (n₁ := n₁) G s G2 (G5, E) b₁ b₂ b₃ (givenSB (pw p₀ n₄) o G3)) (wPre y.2)
        ((z.2.1.2, (z.2.2.1, z.2.2.2, z.1.1)), z.1.2)) ≤
        pr (USh × KS (pw p₀ n₄)) (fun z => bstar Hb G R5 (viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ b₂ b₃ (simSB Hb _ z.2.1.2 z.2.2.1))) := by
      refine pr_mono fun z hz => ?_
      rw [eS z, progRO_fst Hb (withP y.1 (pw p₀ n₄)) z.2.1.2 (shOf z.2.2.2 z.1)]
      unfold mainPredIC mainPred2 at hz
      refine bad₄ Hb G hm R5 _ y z.2.1.2 _ ?_ ?_ ?_ hz

      · simp only [C, viewOf23, ho₁, ho₂, ho₃]
        exact hy
      · simp only [C, viewOf23, ho₁, ho₂, ho₃, hy]
        rfl
      · intro k hk
        dsimp only [tr5] at hk
        rcases mem_union.1 hk with hk | h₄
        · rcases mem_union.1 hk with hk | h₃
          · rcases mem_union.1 hk with h₁ | h₂
            · rcases cov23 Hb k₁ c₁ _ (hv.v₁ _) _ h₁ with h | h
              · exact Or.inl h
              · exact Or.inr (Or.inr (Or.inr (mem_union_left _ (mem_union_left _ h))))
            · rcases cov23 Hb k₂ c₂ _ (hv.v₂ _ _) _ h₂ with h | h
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr (Or.inr (mem_union_left _ (mem_union_right _ h))))
          · rcases cov23 Hb k₃ c₃ _ (hv.v₃ _ _ _) _ h₃ with h | h
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inr (Or.inr (mem_union_right _ h)))
        · simp [givenSB] at h₄
    have hδ : |pr (USh × KS (pw p₀ n₄)) (fun z => Ψ (viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ b₂ b₃ (realSB Hb _ z.2.1.1 z.2.2.1))) -
        pr (USh × KS (pw p₀ n₄)) (fun z => Ψ (C (realRO (pw p₀ n₄) Hb (withP y.1 (pw p₀ n₄)) y.2 z.2.1.1 z.2.2.1
          (shOf z.2.2.2 z.1)) z.2.2 z.1))| ≤ Δ23 p₀.qsDegree := by
      refine (abs_pr_sub_le_of_agree _ _ _ fun z hz => ?_).trans
        (pr_collide_slot Hb hm hp hHb y (hv.v₄ s oa ob oc y hy) (fun u G2 => b₁.pg (G.σ₁ s) u (b₂.pg (G.σ₂ s oa) u (b₃.pg (G.σ₃ s oa ob) u (G2)))) (T₁ ∪ T₂ ∪ T₃) ?_ ?_)
      · rw [eR z, not_not.1 hz]
      · exact (card_union_le _ _).trans ((Nat.add_le_add_right (card_union_le _ _) _).trans (by omega))
      · intro u G2 k hk
        simp only [mem_union, not_or] at hk
        exact (l₁ _ _ _ k hk.1.1).trans ((l₂ _ _ _ k hk.1.2).trans (l₃ _ _ _ k hk.2))
    simp only [eS] at key hbad ⊢
    have := abs_sub_le (pr (USh × KS (pw p₀ n₄)) (fun z => Ψ (viewOf23 (n₁ := n₁) G s z.2.2.2 z.1 b₁ b₂ b₃ (realSB Hb _ z.2.1.1 z.2.2.1))))
      (pr (USh × KS (pw p₀ n₄)) (fun z => Ψ (C (realRO (pw p₀ n₄) Hb (withP y.1 (pw p₀ n₄)) y.2 z.2.1.1 z.2.2.1
          (shOf z.2.2.2 z.1)) z.2.2 z.1)))
      (pr (USh × KS (pw p₀ n₄)) (fun z => Ψ (C (simulate (pw p₀ n₄) z.2.1.2)
          (z.2.2.1, (progRO (pw p₀ n₄) Hb (withP y.1 (pw p₀ n₄)) z.2.1.2 (shOf z.2.2.2 z.1)).1) z.1)))
    linarith

end Hops

end VoleMole.ZK.Sim
