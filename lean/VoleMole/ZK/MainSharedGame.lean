import VoleMole.ZK.MainSharedSlots

/-!
# The joint hop on `main` with one shared `H₅` table and cipher (`lean/docs/zk.md` §4.2)

`main_chain_le` (`ZK/MainGame.lean`) replaces four `main`-layout proofs by simulated ones when each
proof has its own tables. Here the four proofs of a game (`Privacy.MainChain.Game`: each statement
and witness a function of a secret and of the earlier outputs) **share the `H₅` table** (on every
37-byte input) **and the cipher table**; each proof has its own `H₃` slice and its own `H₂³` table,
both visible to the adversary (`VP p`), the latter programmed by the simulator.

## The game (`viewOf`, `hyb`)

Each slot is a behaviour (`Beh`): an output and the slot's visible tables as functions of the
statement and the shared tables, with the keys at which it reads the shared tables (`k5`, `kE`,
`Beh.OK`). `realB` is the executable prover (`realRO`), `simB` the simulator with its programming,
`givenB` a fixed output and fixed tables. `viewOf` runs the four slots in sequence on shared tables
`u` and returns the adversary's view (`GView`: the secret, the shared tables, the outputs, the
slots' tables). `hyb m₁ m₂ m₃ m₄ Ψ` is the probability of the event `Ψ` of the view when slot `j`
is simulated iff `mⱼ`, on **one tape** for all hybrids.

## The hop (`hop₁` … `hop₄`, `step₁` … `step₄`)

The slots are replaced in game order, so the statement of the replaced proof does not depend on
the shared tables (the earlier proofs are simulated). Replacing slot `j` is `slot_zk_main` for the
distinguisher "the rest of the game": its `H₅` read set is the event's own (`R5`) together with the
`H₅` reads of the other slots, the later ones real. The bad event of the hop is therefore that the
witness prefix of proof `j` is a candidate of that set, **on the simulated proof `j`**.

## One bad event for all hops (`bstar`)

`bstar G R5` is an event of the view alone, the same in every hybrid: some proof failed, or for
some proof `j` (with output `b`, witness prefix `r`, label offset `θ = d[0..16) ⊕ r`): `θ = 0`, or
a key of `R5`, or an **active or sibling gate input of another proof**, is a gate input of proof
`j` at offset `θ`. The other proofs' keys are functions of their outputs and witness prefixes
(`proofKeys`); `prove_reads` shows that the real prover reads `H₅` nowhere else, and the
simulator's programming reads the active inputs. So each hop's bad event implies `bstar`
(`pred_imp_bstar`), and `bstar` itself is an event with the read set `R5` (`rd_bstar`) that can be
moved across the later hops.

## The result (`main_shared_le`)

    |Pr[all real; F] − Pr[all simulated; F]| ≤ 15·εS(q₃, q_E + 8·4607) + 15·Pr[all simulated; bstar]

for an event `F` of the view that reads each `H₃` slice at `q₃` keys, the cipher at `q_E` keys and
`H₅` at the keys `R5`, a **consistent** read set (`Rd F R5`, `Rd R5 R5`: changing a table off the
read sets changes neither `F` nor `R5`). `εS q₃ q_E = q₃·2⁻¹²⁸ + 2⁻¹¹³ + 221·(4607 + q_E +
4607)·2⁻¹²⁸`. The factor `15 = 1 + 2 + 4 + 8` is as in `MainChain.fill_ideal_le`: the bad event of
a hop is moved across each later hop, which may double it.
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

/-! ## Behaviours of a slot -/

/-- **A slot's behaviour**: its output on a statement and the shared tables, its visible tables,
and the keys at which these read the shared `H₅` table and cipher. -/
structure Beh (p : Params) where
  run : SW → USh → Out
  vis : Option SW → USh → VP p
  k5 : Option SW → USh → Finset (Bytes 37)
  kE : Option SW → USh → Finset Blk

/-- **A behaviour reads the shared tables only at its keys** (at most `4607` cipher keys), and
reads nothing if there is no statement. -/
structure Beh.OK {p : Params} (b : Beh p) : Prop where
  c5 : ∀ (y : Option SW) (u : USh) (G5 : Tab5F), (∀ k ∈ b.k5 y u, u.1 k = G5 k) →
    (∀ sw ∈ y, b.run sw (G5, u.2) = b.run sw u) ∧ b.vis y (G5, u.2) = b.vis y u
  cE : ∀ (y : Option SW) (u : USh) (E : Cipher), (∀ k ∈ b.kE y u, u.2 k = E k) →
    (∀ sw ∈ y, b.run sw (u.1, E) = b.run sw u) ∧ b.vis y (u.1, E) = b.vis y u
  hE : ∀ y u, (b.kE y u).card ≤ 4607
  k5none : ∀ u, b.k5 none u = ∅

section Behs

variable (Hb : Hashes) (p : Params)

/-- The `H₅` keys the real prover reads. -/
noncomputable def realK5 (ρ : Bytes 16) (v : VP p) (y : Option SW) (u : USh) : Finset (Bytes 37) :=
  match y with
  | some y => realKeys5 p Hb (withP y.1 p) y.2 (ba ρ) v.1 (shOf v.2 u)
  | none => ∅

/-- The cipher keys the real prover reads. -/
noncomputable def realKE (ρ : Bytes 16) (v : VP p) (y : Option SW) (u : USh) : Finset Blk :=
  match y with
  | some y => realKeysE p Hb (withP y.1 p) y.2 (ba ρ) v.1 (shOf v.2 u)
  | none => ∅

/-- **The real prover** with randomness `ρ` and its own tables `v`. -/
noncomputable def realB (ρ : Bytes 16) (v : VP p) : Beh p where
  run y u := realRO p Hb (withP y.1 p) y.2 ρ v.1 (shOf v.2 u)
  vis _ _ := v
  k5 := realK5 Hb p ρ v
  kE := realKE Hb p ρ v

/-- The simulator's visible tables: its `H₂³` table programmed, if a statement is proved. -/
noncomputable def simVis (c : SimCoins p) (v : VP p) (y : Option SW) (u : USh) : VP p :=
  match y with
  | some y => (v.1, (progRO p Hb (withP y.1 p) c (shOf v.2 u)).1)
  | none => v

/-- The `H₅` keys the simulator's programming reads. -/
noncomputable def simK5 (c : SimCoins p) (v : VP p) (y : Option SW) (u : USh) : Finset (Bytes 37) :=
  match y with
  | some y => progKeys5 Hb (withP y.1 p) (simulate p c) (shOf v.2 u)
  | none => ∅

/-- The cipher keys the simulator's programming reads. -/
noncomputable def simKE (c : SimCoins p) (v : VP p) (y : Option SW) (u : USh) : Finset Blk :=
  match y with
  | some y => progKeysE Hb (withP y.1 p) (simulate p c) (shOf v.2 u)
  | none => ∅

/-- **The simulator** with coins `c`: its `H₂³` table is programmed (if a statement is proved). -/
noncomputable def simB (c : SimCoins p) (v : VP p) : Beh p where
  run _ _ := simulate p c
  vis := simVis Hb p c v
  k5 := simK5 Hb p c v
  kE := simKE Hb p c v

/-- **A fixed output and fixed tables.** -/
def givenB (o : Out) (v : VP p) : Beh p where
  run _ _ := o
  vis _ _ := v
  k5 _ _ := ∅
  kE _ _ := ∅

variable {p}

lemma realB_ok (hHb : HashesWF Hb) (ρ : Bytes 16) (v : VP p) : (realB Hb p ρ v).OK where
  c5 y u G5 h := by
    refine ⟨fun sw hsw => ?_, rfl⟩
    cases hsw
    exact realRO_congr5 p Hb (withP sw.1 p) sw.2 ρ v.1 (shOf v.2 u) G5 h
  cE y u E h := by
    refine ⟨fun sw hsw => ?_, rfl⟩
    cases hsw
    exact realRO_congrE p Hb (withP sw.1 p) sw.2 hHb ρ v.1 (shOf v.2 u) E h
  hE y u := by
    rcases y with _ | y
    · simp [realB, realKE]
    · exact card_realKeysE p Hb _ _ _ _ _
  k5none _ := rfl

lemma simB_ok (c : SimCoins p) (v : VP p) : (simB Hb p c v).OK where
  c5 y u G5 h := by
    refine ⟨fun _ _ => rfl, ?_⟩
    rcases y with _ | y
    · rfl
    · exact Prod.ext rfl (progRO_congr5 Hb (withP y.1 p) c (shOf v.2 u) G5 h)
  cE y u E h := by
    refine ⟨fun _ _ => rfl, ?_⟩
    rcases y with _ | y
    · rfl
    · exact Prod.ext rfl (progRO_congrE Hb (withP y.1 p) c (shOf v.2 u) E h)
  hE y u := by
    rcases y with _ | y
    · simp [simB, simKE]
    · exact card_progKeysE Hb _ _ _
  k5none _ := rfl

lemma givenB_ok (o : Out) (v : VP p) : (givenB p o v).OK where
  c5 _ _ _ _ := ⟨fun _ _ => rfl, rfl⟩
  cE _ _ _ _ := ⟨fun _ _ => rfl, rfl⟩
  hE _ _ := by simp [givenB]
  k5none _ := rfl

/-! ## The keys of a proof, and what a behaviour's `H₅` reads are -/

variable (p)

/-- **The `H₅` keys of a proof `b`** for the statement and witness `y`: the verifier's gate inputs
of `b` (the active labels) and the same at the label offset `d[0..16) ⊕ w[0..16)` (the sibling
labels). -/
noncomputable def proofKeys (y : SW) (E : Cipher) (b : ByteArray) : Finset (Bytes 37) :=
  ((@vInOff (icPrg E) Hb CrtGen.tables (withP y.1 p) b W128.zero).toFinset ∪
    (@vInOff (icPrg E) Hb CrtGen.tables (withP y.1 p) b
      (thetaMain (dPre p b) (wPre y.2))).toFinset).image (blk 37)

/-- The keys of a slot from its statement and output (none without a proof). -/
noncomputable def slotKeys (y : Option SW) (o : Option Out) (E : Cipher) : Finset (Bytes 37) :=
  match y, o with
  | some y, some (.ok b) => proofKeys Hb p y E b
  | _, _ => ∅

/-- The slot's proof failed. -/
def slotErr (o : Option Out) : Prop := ∃ e, o = some (.error e)

/-- **A key is a gate input of the slot's proof at its sibling offset**
`thetaMain d[0..16) w[0..16)`. -/
def slotHit (y : Option SW) (o : Option Out) (E : Cipher) (k : Bytes 37) : Prop :=
  match y, o with
  | some y, some (.ok b) => enc5 k ∈ @vInOff (icPrg E) Hb CrtGen.tables (withP y.1 p) b
      (thetaMain (dPre p b) (wPre y.2))
  | _, _ => False

/-- The slot's label offset is zero. -/
def slotZero (y : Option SW) (o : Option Out) : Prop :=
  match y, o with
  | some y, some (.ok b) => thetaMain (dPre p b) (wPre y.2) = W128.zero
  | _, _ => False

variable {p}

/-- **A behaviour's `H₅` keys are keys of its proof** (or it fails), on valid statements. -/
def Beh.Cov (b : Beh p) : Prop :=
  ∀ y, ValidZK CrtGen.tables p y → ∀ u, ∀ k ∈ b.k5 (some y) u,
    slotErr (some (b.run y u)) ∨ k ∈ slotKeys Hb p (some y) (some (b.run y u)) u.2

lemma givenB_cov (o : Out) (v : VP p) : (givenB p o v).Cov Hb := fun _ _ _ k hk => by
  simp [givenB] at hk

lemma simB_cov (c : SimCoins p) (v : VP p) : (simB Hb p c v).Cov Hb := by
  intro y _ u k hk
  show slotErr (some (simulate p c)) ∨ k ∈ slotKeys Hb p (some y) (some (simulate p c)) u.2
  have hk' : k ∈ progKeys5 Hb (withP y.1 p) (simulate p c) (shOf v.2 u) := hk
  unfold progKeys5 at hk'
  rcases ho : simulate p c with e | b
  · exact Or.inl ⟨e, rfl⟩
  · right
    rw [ho] at hk'
    simp only [slotKeys, proofKeys]
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hk'
    refine mem_image.2 ⟨x, mem_union_left _ ?_, rfl⟩
    rw [List.mem_toFinset] at hx ⊢
    have hx2 : x ∈ @vIn5 (icPrg u.2) (rec5 Hb u.1) CrtGen.tables (withP y.1 p) b := hx
    rw [@vIn5_eq_vInOff (icPrg u.2)] at hx2
    rw [← @vInOff_congr (icPrg u.2) (rec5 Hb u.1) CrtGen.tables (withP y.1 p) Hb
      (rec5_mu1 _) (rec5_h4 _)]
    exact hx2

lemma realB_cov (hm : MainP p) (hHb : HashesWF Hb) (ρ : Bytes 16) (v : VP p) :
    (realB Hb p ρ v).Cov Hb := by
  intro y hy u k hk
  obtain ⟨cs, hzk⟩ := hy
  show slotErr (some (realRO p Hb (withP y.1 p) y.2 ρ v.1 (shOf v.2 u))) ∨
    k ∈ slotKeys Hb p (some y) (some (realRO p Hb (withP y.1 p) y.2 ρ v.1 (shOf v.2 u))) u.2
  have hk' : k ∈ realKeys5 p Hb (withP y.1 p) y.2 (ba ρ) v.1 (shOf v.2 u) := hk
  rcases ho : realRO p Hb (withP y.1 p) y.2 ρ v.1 (shOf v.2 u) with e | b
  · exact Or.inl ⟨e, rfl⟩
  · right
    set Hs := recHp p Hb (withP y.1 p) y.2 v.1 v.2 u.1 with hHs
    have hwf : HashesWF Hs := recHp_wf hHb _ _ _
    have hmu : (withP y.1 p).mu1 Hs = (withP y.1 p).mu1 Hb := recHp_mu1 _ _ _
    have ho' : @Prover.prove (icPrg u.2) Hs CrtGen.tables (withP y.1 p) y.2 (ba ρ)
        p.witnessBytes = .ok b := by
      unfold realRO realROb at ho
      exact ho
    have hr := @prove_reads (icPrg u.2) Hs CrtGen.tables (withP y.1 p) y.2 cs hm hzk hwf
      (@bavcComplete (icPrg u.2)) (ba ρ)
      (@crtComplete (icPrg u.2) Hs p ((withP y.1 p).mu1 Hs) (y.2.extract 0 p.witnessBytes) (ba ρ)
        (withP y.1 p).binder1 hm.hlab) b ho'
    simp only [slotKeys, proofKeys]
    unfold realKeys5 at hk'
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hk'
    rw [List.mem_toFinset] at hx
    have hx' := hr x (by
      simp only [rSeed, hmu] at hx ⊢
      exact hx)
    have hc := @vInOff_congr (icPrg u.2) Hs CrtGen.tables (withP y.1 p) Hb hmu (recHp_h4 _ _ _)
    rw [hc] at hx'
    refine mem_image.2 ⟨x, ?_, rfl⟩
    rw [mem_union, List.mem_toFinset, List.mem_toFinset]
    exact hx'

end Behs

/-! ## The view -/

/-- **The adversary's view of a game of four proofs**: the secret, the shared tables, the four
outputs and the four slots' tables. -/
structure GView (S : Type) (p₁ p₂ p₃ p₄ : Params) where
  s : S
  u : USh
  o₁ : Option Out
  o₂ : Option Out
  o₃ : Option Out
  o₄ : Option Out
  v₁ : VP p₁
  v₂ : VP p₂
  v₃ : VP p₃
  v₄ : VP p₄

namespace GView

variable {S : Type} {p₁ p₂ p₃ p₄ : Params} (v : GView S p₁ p₂ p₃ p₄)

/-- The view with other shared tables. -/
def withU (u : USh) : GView S p₁ p₂ p₃ p₄ := { v with u := u }
/-- The view with slot `j`'s `H₃` slice replaced. -/
def with3₁ (G3 : Tab3) : GView S p₁ p₂ p₃ p₄ := { v with v₁ := (G3, v.v₁.2) }
def with3₂ (G3 : Tab3) : GView S p₁ p₂ p₃ p₄ := { v with v₂ := (G3, v.v₂.2) }
def with3₃ (G3 : Tab3) : GView S p₁ p₂ p₃ p₄ := { v with v₃ := (G3, v.v₃.2) }
def with3₄ (G3 : Tab3) : GView S p₁ p₂ p₃ p₄ := { v with v₄ := (G3, v.v₄.2) }

end GView

section Game

variable {S : Type} {p₁ p₂ p₃ p₄ : Params} (G : Game S Out SW SW SW SW)

/-- The four statements of a view. -/
def yv₁ (v : GView S p₁ p₂ p₃ p₄) : Option SW := G.σ₁ v.s
def yv₂ (v : GView S p₁ p₂ p₃ p₄) : Option SW := G.σ₂ v.s v.o₁
def yv₃ (v : GView S p₁ p₂ p₃ p₄) : Option SW := G.σ₃ v.s v.o₁ v.o₂
def yv₄ (v : GView S p₁ p₂ p₃ p₄) : Option SW := G.σ₄ v.s v.o₁ v.o₂ v.o₃

/-- **The view of the game** with the secret `s`, the shared tables `u` and the four behaviours. -/
def viewOf (s : S) (u : USh) (b₁ : Beh p₁) (b₂ : Beh p₂) (b₃ : Beh p₃) (b₄ : Beh p₄) :
    GView S p₁ p₂ p₃ p₄ :=
  let y₁ := G.σ₁ s
  let o₁ := y₁.map (b₁.run · u)
  let y₂ := G.σ₂ s o₁
  let o₂ := y₂.map (b₂.run · u)
  let y₃ := G.σ₃ s o₁ o₂
  let o₃ := y₃.map (b₃.run · u)
  let y₄ := G.σ₄ s o₁ o₂ o₃
  let o₄ := y₄.map (b₄.run · u)
  ⟨s, u, o₁, o₂, o₃, o₄, b₁.vis y₁ u, b₂.vis y₂ u, b₃.vis y₃ u, b₄.vis y₄ u⟩

/-- Two behaviours agree on a statement, at the shared tables `u` and `u'`. -/
def Beh.Agree {p : Params} (b b' : Beh p) (y : Option SW) (u u' : USh) : Prop :=
  (∀ sw ∈ y, b'.run sw u' = b.run sw u) ∧ b'.vis y u' = b.vis y u

lemma Beh.Agree.refl {p : Params} (b : Beh p) (y : Option SW) (u : USh) : b.Agree b y u u :=
  ⟨fun _ _ => rfl, rfl⟩

/-- **The view is determined slot by slot**: behaviours (and shared tables) that agree on the
statements of a run give the same view, up to the shared tables. -/
theorem viewOf_agree (s : S) (u u' : USh) (b₁ b₁' : Beh p₁) (b₂ b₂' : Beh p₂) (b₃ b₃' : Beh p₃)
    (b₄ b₄' : Beh p₄)
    (h₁ : b₁.Agree b₁' (yv₁ G (viewOf G s u b₁ b₂ b₃ b₄)) u u')
    (h₂ : b₂.Agree b₂' (yv₂ G (viewOf G s u b₁ b₂ b₃ b₄)) u u')
    (h₃ : b₃.Agree b₃' (yv₃ G (viewOf G s u b₁ b₂ b₃ b₄)) u u')
    (h₄ : b₄.Agree b₄' (yv₄ G (viewOf G s u b₁ b₂ b₃ b₄)) u u') :
    viewOf G s u' b₁' b₂' b₃' b₄' = (viewOf G s u b₁ b₂ b₃ b₄).withU u' := by
  have e₁ : (G.σ₁ s).map (b₁'.run · u') = (G.σ₁ s).map (b₁.run · u) :=
    Option.map_congr fun sw hsw => h₁.1 sw hsw
  have e₂ : (G.σ₂ s ((G.σ₁ s).map (b₁.run · u))).map (b₂'.run · u') =
      (G.σ₂ s ((G.σ₁ s).map (b₁.run · u))).map (b₂.run · u) :=
    Option.map_congr fun sw hsw => h₂.1 sw hsw
  have e₃ : (G.σ₃ s ((G.σ₁ s).map (b₁.run · u))
        ((G.σ₂ s ((G.σ₁ s).map (b₁.run · u))).map (b₂.run · u))).map (b₃'.run · u') =
      (G.σ₃ s ((G.σ₁ s).map (b₁.run · u))
        ((G.σ₂ s ((G.σ₁ s).map (b₁.run · u))).map (b₂.run · u))).map (b₃.run · u) :=
    Option.map_congr fun sw hsw => h₃.1 sw hsw
  have e₄ : (G.σ₄ s ((G.σ₁ s).map (b₁.run · u))
        ((G.σ₂ s ((G.σ₁ s).map (b₁.run · u))).map (b₂.run · u))
        ((G.σ₃ s ((G.σ₁ s).map (b₁.run · u))
          ((G.σ₂ s ((G.σ₁ s).map (b₁.run · u))).map (b₂.run · u))).map (b₃.run · u))).map
          (b₄'.run · u') =
      (G.σ₄ s ((G.σ₁ s).map (b₁.run · u))
        ((G.σ₂ s ((G.σ₁ s).map (b₁.run · u))).map (b₂.run · u))
        ((G.σ₃ s ((G.σ₁ s).map (b₁.run · u))
          ((G.σ₂ s ((G.σ₁ s).map (b₁.run · u))).map (b₂.run · u))).map (b₃.run · u))).map
          (b₄.run · u) :=
    Option.map_congr fun sw hsw => h₄.1 sw hsw
  have f₁ := h₁.2
  have f₂ := h₂.2
  have f₃ := h₃.2
  have f₄ := h₄.2
  simp only [yv₁, yv₂, yv₃, yv₄, viewOf] at f₁ f₂ f₃ f₄
  simp only [viewOf, GView.withU, e₁, e₂, e₃, e₄, f₁, f₂, f₃, f₄]

/-- The `H₅` keys the four behaviours read on a view. -/
def traceK5 (b₁ : Beh p₁) (b₂ : Beh p₂) (b₃ : Beh p₃) (b₄ : Beh p₄) (v : GView S p₁ p₂ p₃ p₄) :
    Finset (Bytes 37) :=
  b₁.k5 (yv₁ G v) v.u ∪ b₂.k5 (yv₂ G v) v.u ∪ b₃.k5 (yv₃ G v) v.u ∪ b₄.k5 (yv₄ G v) v.u

/-- The cipher keys the four behaviours read on a view. -/
def traceKE (b₁ : Beh p₁) (b₂ : Beh p₂) (b₃ : Beh p₃) (b₄ : Beh p₄) (v : GView S p₁ p₂ p₃ p₄) :
    Finset Blk :=
  b₁.kE (yv₁ G v) v.u ∪ b₂.kE (yv₂ G v) v.u ∪ b₃.kE (yv₃ G v) v.u ∪ b₄.kE (yv₄ G v) v.u

lemma card_traceKE {b₁ : Beh p₁} {b₂ : Beh p₂} {b₃ : Beh p₃} {b₄ : Beh p₄} (k₁ : b₁.OK)
    (k₂ : b₂.OK) (k₃ : b₃.OK) (k₄ : b₄.OK) (v : GView S p₁ p₂ p₃ p₄) :
    (traceKE G b₁ b₂ b₃ b₄ v).card ≤ 4 * 4607 := by
  unfold traceKE
  have h₁ := k₁.hE (yv₁ G v) v.u
  have h₂ := k₂.hE (yv₂ G v) v.u
  have h₃ := k₃.hE (yv₃ G v) v.u
  have h₄ := k₄.hE (yv₄ G v) v.u
  have a := card_union_le (b₁.kE (yv₁ G v) v.u ∪ b₂.kE (yv₂ G v) v.u ∪ b₃.kE (yv₃ G v) v.u)
    (b₄.kE (yv₄ G v) v.u)
  have b := card_union_le (b₁.kE (yv₁ G v) v.u ∪ b₂.kE (yv₂ G v) v.u) (b₃.kE (yv₃ G v) v.u)
  have c := card_union_le (b₁.kE (yv₁ G v) v.u) (b₂.kE (yv₂ G v) v.u)
  omega

/-- **Changing the `H₅` table off the behaviours' keys** changes the view only in that table. -/
theorem viewOf_G5 (s : S) (u : USh) {b₁ : Beh p₁} {b₂ : Beh p₂} {b₃ : Beh p₃} {b₄ : Beh p₄}
    (k₁ : b₁.OK) (k₂ : b₂.OK) (k₃ : b₃.OK) (k₄ : b₄.OK) (G5 : Tab5F)
    (h : ∀ k ∈ traceK5 G b₁ b₂ b₃ b₄ (viewOf G s u b₁ b₂ b₃ b₄), u.1 k = G5 k) :
    viewOf G s (G5, u.2) b₁ b₂ b₃ b₄ = (viewOf G s u b₁ b₂ b₃ b₄).withU (G5, u.2) := by
  unfold traceK5 at h
  simp only [mem_union] at h
  exact viewOf_agree G s u (G5, u.2) b₁ b₁ b₂ b₂ b₃ b₃ b₄ b₄
    (k₁.c5 _ u G5 fun k hk => h k (Or.inl (Or.inl (Or.inl hk))))
    (k₂.c5 _ u G5 fun k hk => h k (Or.inl (Or.inl (Or.inr hk))))
    (k₃.c5 _ u G5 fun k hk => h k (Or.inl (Or.inr hk)))
    (k₄.c5 _ u G5 fun k hk => h k (Or.inr hk))

/-- **Changing the cipher off the behaviours' keys** changes the view only in that table. -/
theorem viewOf_E (s : S) (u : USh) {b₁ : Beh p₁} {b₂ : Beh p₂} {b₃ : Beh p₃} {b₄ : Beh p₄}
    (k₁ : b₁.OK) (k₂ : b₂.OK) (k₃ : b₃.OK) (k₄ : b₄.OK) (E : Cipher)
    (h : ∀ k ∈ traceKE G b₁ b₂ b₃ b₄ (viewOf G s u b₁ b₂ b₃ b₄), u.2 k = E k) :
    viewOf G s (u.1, E) b₁ b₂ b₃ b₄ = (viewOf G s u b₁ b₂ b₃ b₄).withU (u.1, E) := by
  unfold traceKE at h
  simp only [mem_union] at h
  exact viewOf_agree G s u (u.1, E) b₁ b₁ b₂ b₂ b₃ b₃ b₄ b₄
    (k₁.cE _ u E fun k hk => h k (Or.inl (Or.inl (Or.inl hk))))
    (k₂.cE _ u E fun k hk => h k (Or.inl (Or.inl (Or.inr hk))))
    (k₃.cE _ u E fun k hk => h k (Or.inl (Or.inr hk)))
    (k₄.cE _ u E fun k hk => h k (Or.inr hk))

end Game

end VoleMole.ZK.Sim
