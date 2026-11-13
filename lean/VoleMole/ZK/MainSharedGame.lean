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


/-! ## Events of the view and their read sets -/

section Events

variable {S : Type} {p₁ p₂ p₃ p₄ : Params}

/-- **`f` reads the tables of a view within explicit sets**: the `H₅` table only at `R5`, the
cipher at `qE` keys, each `H₃` slice at `q3` keys (the `H₂³` tables freely). -/
structure Rd {X : Sort*} (f : GView S p₁ p₂ p₃ p₄ → X)
    (R5 : GView S p₁ p₂ p₃ p₄ → Finset (Bytes 37)) (q3 qE : ℕ) : Prop where
  h5 : ∀ v (G5 : Tab5F), (∀ k ∈ R5 v, v.u.1 k = G5 k) → f (v.withU (G5, v.u.2)) = f v
  hE : ∃ Q : GView S p₁ p₂ p₃ p₄ → Finset Blk, (∀ v, (Q v).card ≤ qE) ∧
    ∀ v (E : Cipher), (∀ k ∈ Q v, v.u.2 k = E k) → f (v.withU (v.u.1, E)) = f v
  h3₁ : ∃ Q : GView S p₁ p₂ p₃ p₄ → Finset (Bytes 16), (∀ v, (Q v).card ≤ q3) ∧
    ∀ v (G3 : Tab3), (∀ k ∈ Q v, v.v₁.1 k = G3 k) → f (v.with3₁ G3) = f v
  h3₂ : ∃ Q : GView S p₁ p₂ p₃ p₄ → Finset (Bytes 16), (∀ v, (Q v).card ≤ q3) ∧
    ∀ v (G3 : Tab3), (∀ k ∈ Q v, v.v₂.1 k = G3 k) → f (v.with3₂ G3) = f v
  h3₃ : ∃ Q : GView S p₁ p₂ p₃ p₄ → Finset (Bytes 16), (∀ v, (Q v).card ≤ q3) ∧
    ∀ v (G3 : Tab3), (∀ k ∈ Q v, v.v₃.1 k = G3 k) → f (v.with3₃ G3) = f v
  h3₄ : ∃ Q : GView S p₁ p₂ p₃ p₄ → Finset (Bytes 16), (∀ v, (Q v).card ≤ q3) ∧
    ∀ v (G3 : Tab3), (∀ k ∈ Q v, v.v₄.1 k = G3 k) → f (v.with3₄ G3) = f v

variable (Hb : Hashes)

/-- The cipher keys that the keys of a slot's proof read (the reconstruction's nodes). -/
noncomputable def slotRd (p : Params) (y : Option SW) (o : Option Out) (E : Cipher) : Finset Blk :=
  match y, o with
  | some y, some (.ok b) => rdKeys E (ivOf Hb ⟨p, b⟩ ((withP y.1 p).mu1 Hb))
      (⟨p, b⟩ : Proof).opening (⟨p, b⟩ : Proof).delta
  | _, _ => ∅

lemma card_slotRd (p : Params) (y : Option SW) (o : Option Out) (E : Cipher) :
    (slotRd Hb p y o E).card ≤ 4607 := by
  unfold slotRd
  split
  · exact rdKeys_card _ _ _ _
  · simp

lemma slotKeys_congrE (p : Params) (y : Option SW) (o : Option Out) {E E' : Cipher}
    (h : ∀ k ∈ slotRd Hb p y o E, E k = E' k) : slotKeys Hb p y o E' = slotKeys Hb p y o E := by
  unfold slotKeys
  unfold slotRd at h
  split
  · rename_i y b
    simp only [proofKeys]
    rw [vInOff_ic_congr Hb CrtGen.tables (withP y.1 p) b _ h,
      vInOff_ic_congr Hb CrtGen.tables (withP y.1 p) b _ h]
  · rfl

lemma slotHit_congrE (p : Params) (y : Option SW) (o : Option Out) {E E' : Cipher}
    (h : ∀ k ∈ slotRd Hb p y o E, E k = E' k) : slotHit Hb p y o E' = slotHit Hb p y o E := by
  funext k
  unfold slotHit
  unfold slotRd at h
  split
  · rename_i y b
    rw [vInOff_ic_congr Hb CrtGen.tables (withP y.1 p) b _ h]
  · rfl

variable (G : Game S Out SW SW SW SW)

/-- **The bad event, on the outputs** (`bstar`): some proof failed, or for some proof its label
offset is zero, or a key of `R` or a key of another proof is a gate input of the proof at its
sibling offset. -/
def bstarCore (s : S) (o₁ o₂ o₃ o₄ : Option Out) (E : Cipher) (R : Finset (Bytes 37)) : Prop :=
  (slotErr o₁ ∨ slotErr o₂ ∨ slotErr o₃ ∨ slotErr o₄) ∨
  (slotZero p₁ (G.σ₁ s) o₁ ∨ ∃ k ∈ R ∪ (slotKeys Hb p₂ (G.σ₂ s o₁) o₂ E ∪
      slotKeys Hb p₃ (G.σ₃ s o₁ o₂) o₃ E ∪ slotKeys Hb p₄ (G.σ₄ s o₁ o₂ o₃) o₄ E),
    slotHit Hb p₁ (G.σ₁ s) o₁ E k) ∨
  (slotZero p₂ (G.σ₂ s o₁) o₂ ∨ ∃ k ∈ R ∪ (slotKeys Hb p₁ (G.σ₁ s) o₁ E ∪
      slotKeys Hb p₃ (G.σ₃ s o₁ o₂) o₃ E ∪ slotKeys Hb p₄ (G.σ₄ s o₁ o₂ o₃) o₄ E),
    slotHit Hb p₂ (G.σ₂ s o₁) o₂ E k) ∨
  (slotZero p₃ (G.σ₃ s o₁ o₂) o₃ ∨ ∃ k ∈ R ∪ (slotKeys Hb p₁ (G.σ₁ s) o₁ E ∪
      slotKeys Hb p₂ (G.σ₂ s o₁) o₂ E ∪ slotKeys Hb p₄ (G.σ₄ s o₁ o₂ o₃) o₄ E),
    slotHit Hb p₃ (G.σ₃ s o₁ o₂) o₃ E k) ∨
  (slotZero p₄ (G.σ₄ s o₁ o₂ o₃) o₄ ∨ ∃ k ∈ R ∪ (slotKeys Hb p₁ (G.σ₁ s) o₁ E ∪
      slotKeys Hb p₂ (G.σ₂ s o₁) o₂ E ∪ slotKeys Hb p₃ (G.σ₃ s o₁ o₂) o₃ E),
    slotHit Hb p₄ (G.σ₄ s o₁ o₂ o₃) o₄ E k)

/-- **The bad event of the joint hop**, an event of the view (the same in every hybrid). -/
def bstar (R5 : GView S p₁ p₂ p₃ p₄ → Finset (Bytes 37)) (v : GView S p₁ p₂ p₃ p₄) : Prop :=
  bstarCore (p₁ := p₁) (p₂ := p₂) (p₃ := p₃) (p₄ := p₄) Hb G v.s v.o₁ v.o₂ v.o₃ v.o₄ v.u.2 (R5 v)

/-- **The bad event reads what `R5` reads**, and the cipher at `4·4607` more keys (the
reconstructions of the four proofs). -/
theorem rd_bstar {R5 : GView S p₁ p₂ p₃ p₄ → Finset (Bytes 37)} {q3 qE : ℕ}
    (hR : Rd R5 R5 q3 qE) : Rd (bstar Hb G R5) R5 q3 (qE + 4 * 4607) := by
  classical
  refine ⟨fun v G5 h => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show bstarCore Hb G _ _ _ _ _ _ (R5 (v.withU (G5, v.u.2))) = _
    rw [hR.h5 v G5 h]; rfl
  · obtain ⟨Q, hQc, hQ⟩ := hR.hE
    refine ⟨fun v => Q v ∪ (slotRd Hb p₁ (yv₁ G v) v.o₁ v.u.2 ∪ slotRd Hb p₂ (yv₂ G v) v.o₂ v.u.2 ∪
      slotRd Hb p₃ (yv₃ G v) v.o₃ v.u.2 ∪ slotRd Hb p₄ (yv₄ G v) v.o₄ v.u.2), fun v => ?_,
      fun v E h => ?_⟩
    · have a₁ := card_slotRd Hb p₁ (yv₁ G v) v.o₁ v.u.2
      have a₂ := card_slotRd Hb p₂ (yv₂ G v) v.o₂ v.u.2
      have a₃ := card_slotRd Hb p₃ (yv₃ G v) v.o₃ v.u.2
      have a₄ := card_slotRd Hb p₄ (yv₄ G v) v.o₄ v.u.2
      have b₀ := card_union_le (Q v) (slotRd Hb p₁ (yv₁ G v) v.o₁ v.u.2 ∪
        slotRd Hb p₂ (yv₂ G v) v.o₂ v.u.2 ∪ slotRd Hb p₃ (yv₃ G v) v.o₃ v.u.2 ∪
        slotRd Hb p₄ (yv₄ G v) v.o₄ v.u.2)
      have b₁ := card_union_le (slotRd Hb p₁ (yv₁ G v) v.o₁ v.u.2 ∪
        slotRd Hb p₂ (yv₂ G v) v.o₂ v.u.2 ∪ slotRd Hb p₃ (yv₃ G v) v.o₃ v.u.2)
        (slotRd Hb p₄ (yv₄ G v) v.o₄ v.u.2)
      have b₂ := card_union_le (slotRd Hb p₁ (yv₁ G v) v.o₁ v.u.2 ∪
        slotRd Hb p₂ (yv₂ G v) v.o₂ v.u.2) (slotRd Hb p₃ (yv₃ G v) v.o₃ v.u.2)
      have b₃ := card_union_le (slotRd Hb p₁ (yv₁ G v) v.o₁ v.u.2)
        (slotRd Hb p₂ (yv₂ G v) v.o₂ v.u.2)
      have := hQc v
      beta_reduce
      omega
    · simp only [mem_union] at h
      have e₁ := slotKeys_congrE Hb p₁ (yv₁ G v) v.o₁ (E := v.u.2) (E' := E)
        fun k hk => h k (Or.inr (Or.inl (Or.inl (Or.inl hk))))
      have e₂ := slotKeys_congrE Hb p₂ (yv₂ G v) v.o₂ (E := v.u.2) (E' := E)
        fun k hk => h k (Or.inr (Or.inl (Or.inl (Or.inr hk))))
      have e₃ := slotKeys_congrE Hb p₃ (yv₃ G v) v.o₃ (E := v.u.2) (E' := E)
        fun k hk => h k (Or.inr (Or.inl (Or.inr hk)))
      have e₄ := slotKeys_congrE Hb p₄ (yv₄ G v) v.o₄ (E := v.u.2) (E' := E)
        fun k hk => h k (Or.inr (Or.inr hk))
      have f₁ := slotHit_congrE Hb p₁ (yv₁ G v) v.o₁ (E := v.u.2) (E' := E)
        fun k hk => h k (Or.inr (Or.inl (Or.inl (Or.inl hk))))
      have f₂ := slotHit_congrE Hb p₂ (yv₂ G v) v.o₂ (E := v.u.2) (E' := E)
        fun k hk => h k (Or.inr (Or.inl (Or.inl (Or.inr hk))))
      have f₃ := slotHit_congrE Hb p₃ (yv₃ G v) v.o₃ (E := v.u.2) (E' := E)
        fun k hk => h k (Or.inr (Or.inl (Or.inr hk)))
      have f₄ := slotHit_congrE Hb p₄ (yv₄ G v) v.o₄ (E := v.u.2) (E' := E)
        fun k hk => h k (Or.inr (Or.inr hk))
      simp only [yv₁, yv₂, yv₃, yv₄] at e₁ e₂ e₃ e₄ f₁ f₂ f₃ f₄
      show bstarCore Hb G v.s v.o₁ v.o₂ v.o₃ v.o₄ E (R5 (v.withU (v.u.1, E))) = _
      rw [hQ v E fun k hk => h k (Or.inl hk)]
      simp only [bstar, bstarCore, e₁, e₂, e₃, e₄, f₁, f₂, f₃, f₄]
  · obtain ⟨Q, hQc, hQ⟩ := hR.h3₁
    refine ⟨Q, hQc, fun v G3 h => ?_⟩
    show bstarCore Hb G _ _ _ _ _ _ (R5 (v.with3₁ G3)) = _
    rw [hQ v G3 h]; rfl
  · obtain ⟨Q, hQc, hQ⟩ := hR.h3₂
    refine ⟨Q, hQc, fun v G3 h => ?_⟩
    show bstarCore Hb G _ _ _ _ _ _ (R5 (v.with3₂ G3)) = _
    rw [hQ v G3 h]; rfl
  · obtain ⟨Q, hQc, hQ⟩ := hR.h3₃
    refine ⟨Q, hQc, fun v G3 h => ?_⟩
    show bstarCore Hb G _ _ _ _ _ _ (R5 (v.with3₃ G3)) = _
    rw [hQ v G3 h]; rfl
  · obtain ⟨Q, hQc, hQ⟩ := hR.h3₄
    refine ⟨Q, hQc, fun v G3 h => ?_⟩
    show bstarCore Hb G _ _ _ _ _ _ (R5 (v.with3₄ G3)) = _
    rw [hQ v G3 h]; rfl

end Events


/-! ## Replacing one proof, the rest of the game as the distinguisher -/

section Ctx

variable {S : Type} {p₁ p₂ p₃ p₄ : Params} (Hb : Hashes)

/-- Averaging a per-fiber bound `ε + Pr[B]`. -/
theorem abs_pr_fiber_le {α β : Type*} [Fintype α] [Nonempty α] [Fintype β]
    (P Q B : α × β → Prop) {ε : ℝ}
    (h : ∀ a, |pr β (fun b => P (a, b)) - pr β (fun b => Q (a, b))| ≤ ε + pr β (fun b => B (a, b))) :
    |pr (α × β) P - pr (α × β) Q| ≤ ε + pr (α × β) B := by
  have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  rw [pr_prod, pr_prod, pr_prod, ← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hα,
    div_le_iff₀ hα, add_mul, div_mul_cancel₀ _ hα.ne']
  calc |∑ a, (pr β (fun b => P (a, b)) - pr β (fun b => Q (a, b)))|
      ≤ ∑ a, |pr β (fun b => P (a, b)) - pr β (fun b => Q (a, b))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : α, (ε + pr β (fun b => B (a, b))) := Finset.sum_le_sum fun a _ => h a
    _ = ε * Fintype.card α + ∑ a, pr β (fun b => B (a, b)) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

/-- **One proof replaced, in a context.** `C o V u` is the view of the game when this proof's
output is `o`, its tables are `V` and the shared tables are `u`; the rest of the game reads the
shared tables at `T5`, `TE`. For an event `Ψ` that reads `H₅` at `R5`, the real proof and the
simulated one differ by `εS` and the probability that the witness prefix is a candidate of
`R5 ∪ T5` on the simulated proof. -/
theorem ctx_hop {p : Params} (hm : MainP p) (hp : SmallParams p) (hHb : HashesWF Hb) (y : SW)
    (hy : ValidZK CrtGen.tables p y) (Ψ : GView S p₁ p₂ p₃ p₄ → Prop)
    (R5 : GView S p₁ p₂ p₃ p₄ → Finset (Bytes 37))
    (C : Out → VP p → USh → GView S p₁ p₂ p₃ p₄)
    (T5 : Out → VP p → USh → Finset (Bytes 37)) (TE : Out → VP p → USh → Finset Blk)
    (hCu : ∀ o V u, (C o V u).u = u)
    (hC5 : ∀ o V u (G5 : Tab5F), (∀ k ∈ T5 o V u, u.1 k = G5 k) →
      C o V (G5, u.2) = (C o V u).withU (G5, u.2))
    (hCE : ∀ o V u (E : Cipher), (∀ k ∈ TE o V u, u.2 k = E k) →
      C o V (u.1, E) = (C o V u).withU (u.1, E))
    (hTE : ∀ o V u, (TE o V u).card ≤ 4 * 4607)
    (set3 : GView S p₁ p₂ p₃ p₄ → Tab3 → GView S p₁ p₂ p₃ p₄)
    (get3 : GView S p₁ p₂ p₃ p₄ → Tab3)
    (hC3 : ∀ o (G3 G3' : Tab3) (G2 : Tab2G p) u,
      C o (G3', G2) u = set3 (C o (G3, G2) u) G3' ∧ get3 (C o (G3, G2) u) = G3)
    {q3 qE : ℕ}
    (hΨ5 : ∀ v (G5 : Tab5F), (∀ k ∈ R5 v, v.u.1 k = G5 k) → Ψ (v.withU (G5, v.u.2)) = Ψ v)
    (hΨE : ∃ Q : GView S p₁ p₂ p₃ p₄ → Finset Blk, (∀ v, (Q v).card ≤ qE) ∧
      ∀ v (E : Cipher), (∀ k ∈ Q v, v.u.2 k = E k) → Ψ (v.withU (v.u.1, E)) = Ψ v)
    (hΨ3 : ∃ Q : GView S p₁ p₂ p₃ p₄ → Finset (Bytes 16), (∀ v, (Q v).card ≤ q3) ∧
      ∀ v (G3 : Tab3), (∀ k ∈ Q v, get3 v k = G3 k) → Ψ (set3 v G3) = Ψ v) :
    |pr (USh × KS p) (fun z => Ψ (C (realRO p Hb (withP y.1 p) y.2 z.2.1.1 z.2.2.1
          (shOf z.2.2.2 z.1)) z.2.2 z.1)) -
      pr (USh × KS p) (fun z => Ψ (C (simulate p z.2.1.2)
          (z.2.2.1, (progRO p Hb (withP y.1 p) z.2.1.2 (shOf z.2.2.2 z.1)).1) z.1))| ≤
      εS q3 (qE + 4 * 4607) + pr (USh × KS p) (fun z => mainPredIC Hb (withP y.1 p) hm
        (fun o G3 G2 G5 E => R5 (C o (G3, G2) (G5, E)) ∪ T5 o (G3, G2) (G5, E)) (wPre y.2)
        ((z.2.1.2, (z.2.2.1, z.2.2.2, z.1.1)), z.1.2)) := by
  classical
  obtain ⟨cs, hzk⟩ := hy
  obtain ⟨QE, hQEc, hQE⟩ := hΨE
  obtain ⟨Q3, hQ3c, hQ3⟩ := hΨ3
  refine slot_zk_main Hb (withP y.1 p) y.2 hm hzk hHb hp
    (fun o G3 G2 G5 E => Ψ (C o (G3, G2) (G5, E)))
    (fun o G3 G2 G5 E => Q3 (C o (G3, G2) (G5, E))) ?_ (fun _ _ _ _ _ => hQ3c _)
    (fun o G3 G2 G5 E => R5 (C o (G3, G2) (G5, E)) ∪ T5 o (G3, G2) (G5, E)) ?_
    (fun o G3 G2 G5 E => QE (C o (G3, G2) (G5, E)) ∪ TE o (G3, G2) (G5, E)) ?_ ?_
  · intro o G3 G3' G2 G5 E h
    obtain ⟨e1, e2⟩ := hC3 o G3 G3' G2 (G5, E)
    rw [e1, hQ3 _ G3' (by rw [e2]; exact h)]
  · intro o G3 G2 G5 G5' E h
    have e := hC5 o (G3, G2) (G5, E) G5' fun k hk => h k (mem_union_right _ hk)
    have hu := hCu o (G3, G2) (G5, E)
    have := hΨ5 (C o (G3, G2) (G5, E)) G5' (by
      rw [hu]; exact fun k hk => h k (mem_union_left _ hk))
    rw [hu] at this
    rw [e, this]
  · intro o G3 G2 G5 E E' h
    have e := hCE o (G3, G2) (G5, E) E' fun k hk => h k (mem_union_right _ hk)
    have hu := hCu o (G3, G2) (G5, E)
    have := hQE (C o (G3, G2) (G5, E)) E' (by
      rw [hu]; exact fun k hk => h k (mem_union_left _ hk))
    rw [hu] at this
    rw [e, this]
  · intro o G3 G2 G5 E
    exact (card_union_le _ _).trans (add_le_add (hQEc _) (hTE _ _ _))

set_option maxRecDepth 4000 in
/-- **The bad event of `ctx_hop`, on the simulated proof**: the simulation failed, or its label
offset is zero, or a key of the read set is a gate input of the simulated proof at its sibling
offset. -/
theorem pred_imp [HasPrg] {p : Params} (hm : MainP p) (y : SW) (c : SimCoins p)
    (Sx : Finset (Bytes 37))
    (h : wPre y.2 ∈ candidatesG Hb CrtGen.tables (withP y.1 p) enc5 hm Sx c.1 c.2) :
    slotErr (some (simulate p c)) ∨ slotZero p (some y) (some (simulate p c)) ∨
      ∃ k ∈ Sx, enc5 k ∈ match simulate p c with
        | .ok b => vInOff Hb CrtGen.tables (withP y.1 p) b (thetaMain (dPre p b) (wPre y.2))
        | .error _ => [] := by
  rcases hf : firstHit c.1.2.1 with _ | ⟨ctr, δ⟩
  · left
    refine ⟨"grinding failed", ?_⟩
    unfold simulate
    rw [hf]
  · have ho : simulate p c = .ok (simAssemble p c.1 ctr δ c.2) := by
      unfold simulate
      rw [hf]
      rfl
    right
    have hc := cand_imp Hb CrtGen.tables (withP y.1 p) hm Sx c.1 c.2 hf h
    rcases hc with hz | ⟨k, hk, hx⟩
    · left
      rw [ho]
      exact hz
    · right
      refine ⟨k, hk, ?_⟩
      rw [ho]
      exact hx

end Ctx


/-! ## The four hops -/

section Hops

variable {S : Type} {p₁ p₂ p₃ p₄ : Params} (Hb : Hashes) (G : Game S Out SW SW SW SW)

/-- **Every statement of the game is valid** (some system for which the deterministic hypotheses
hold). -/
structure GValid (G : Game S Out SW SW SW SW) (p₁ p₂ p₃ p₄ : Params) : Prop where
  v₁ : ∀ s, ∀ y ∈ G.σ₁ s, ValidZK CrtGen.tables p₁ y
  v₂ : ∀ s o₁, ∀ y ∈ G.σ₂ s o₁, ValidZK CrtGen.tables p₂ y
  v₃ : ∀ s o₁ o₂, ∀ y ∈ G.σ₃ s o₁ o₂, ValidZK CrtGen.tables p₃ y
  v₄ : ∀ s o₁ o₂ o₃, ∀ y ∈ G.σ₄ s o₁ o₂ o₃, ValidZK CrtGen.tables p₄ y

variable {Hb}

/-- A behaviour's `H₅` keys on a statement are keys of its proof, or the proof failed. -/
lemma cov_view {p : Params} {b : Beh p} (hk : b.OK) (hc : b.Cov Hb) (y : Option SW)
    (hy : ∀ sw ∈ y, ValidZK CrtGen.tables p sw) (u : USh) {k : Bytes 37} (h : k ∈ b.k5 y u) :
    slotErr (y.map (b.run · u)) ∨ k ∈ slotKeys Hb p y (y.map (b.run · u)) u.2 := by
  rcases y with _ | sw
  · rw [hk.k5none] at h; simp at h
  · exact hc sw (hy sw rfl) u k h

lemma slotHit_of {p : Params} (y : SW) (o : Out) (E : Cipher) (k : Bytes 37)
    (h : enc5 k ∈ match o with
      | .ok b => @vInOff (icPrg E) Hb CrtGen.tables (withP y.1 p) b (thetaMain (dPre p b) (wPre y.2))
      | .error _ => []) : slotHit Hb p (some y) (some o) E k := by
  rcases o with e | b
  · simp at h
  · exact h

/-- A hit by a key of the event's read set or of the other slots' reads is a hit by a key of the
read set or of the other slots' proofs, unless one of them failed. -/
lemma hit_others {R T Kx Ky Kz : Finset (Bytes 37)} {P : Bytes 37 → Prop} {ex ey ez : Prop}
    (h : ∃ k ∈ R ∪ T, P k) (hT : ∀ k ∈ T, ex ∨ ey ∨ ez ∨ k ∈ Kx ∪ Ky ∪ Kz) :
    (ex ∨ ey ∨ ez) ∨ ∃ k ∈ R ∪ (Kx ∪ Ky ∪ Kz), P k := by
  obtain ⟨k, hk, hP⟩ := h
  rcases mem_union.1 hk with hk | hk
  · exact Or.inr ⟨k, mem_union_left _ hk, hP⟩
  · rcases hT k hk with h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr h))
    · exact Or.inr ⟨k, mem_union_right _ h, hP⟩

lemma withU_self (v : GView S p₁ p₂ p₃ p₄) : v.withU v.u = v := rfl

variable (Hb)

set_option maxRecDepth 8000 in
/-- **Replacing the first proof**. -/
theorem hop₁ (hm : MainP p₁) (hp : SmallParams p₁) (hHb : HashesWF Hb)
    (hv : GValid G p₁ p₂ p₃ p₄) (Ψ : GView S p₁ p₂ p₃ p₄ → Prop)
    (R5 : GView S p₁ p₂ p₃ p₄ → Finset (Bytes 37)) {q3 qE : ℕ} (hΨ : Rd Ψ R5 q3 qE) (s : S)
    (b₂ : Beh p₂) (b₃ : Beh p₃) (b₄ : Beh p₄) (k₂ : b₂.OK) (k₃ : b₃.OK) (k₄ : b₄.OK)
    (c₂ : b₂.Cov Hb) (c₃ : b₃.Cov Hb) (c₄ : b₄.Cov Hb) :
    |pr (USh × KS p₁) (fun z => Ψ (viewOf G s z.1 (realB Hb p₁ z.2.1.1 z.2.2) b₂ b₃ b₄)) -
      pr (USh × KS p₁) (fun z => Ψ (viewOf G s z.1 (simB Hb p₁ z.2.1.2 z.2.2) b₂ b₃ b₄))| ≤
      εS q3 (qE + 4 * 4607) + pr (USh × KS p₁) (fun z =>
        bstar Hb G R5 (viewOf G s z.1 (simB Hb p₁ z.2.1.2 z.2.2) b₂ b₃ b₄)) := by
  classical
  rcases hy : G.σ₁ s with _ | y
  · have e : ∀ z : USh × KS p₁, viewOf G s z.1 (simB Hb p₁ z.2.1.2 z.2.2) b₂ b₃ b₄ =
        viewOf G s z.1 (realB Hb p₁ z.2.1.1 z.2.2) b₂ b₃ b₄ := by
      intro z
      refine viewOf_agree G s z.1 z.1 (realB Hb p₁ z.2.1.1 z.2.2)
        (simB Hb p₁ z.2.1.2 z.2.2) b₂ b₂ b₃ b₃ b₄ b₄
        ⟨fun sw hsw => ?_, ?_⟩ (Beh.Agree.refl _ _ _) (Beh.Agree.refl _ _ _) (Beh.Agree.refl _ _ _)
      · have : sw ∈ G.σ₁ s := hsw
        rw [hy] at this; cases this
      · show simVis Hb p₁ z.2.1.2 z.2.2 (G.σ₁ s) z.1 = z.2.2
        rw [hy]; rfl
    simp only [e, sub_self, abs_zero]
    exact add_nonneg (εS_nonneg _ _) (pr_nonneg _)
  · set C : Out → VP p₁ → USh → GView S p₁ p₂ p₃ p₄ :=
      fun o V u => viewOf G s u (givenB p₁ o V) b₂ b₃ b₄ with hC
    have eR : ∀ z : USh × KS p₁, viewOf G s z.1 (realB Hb p₁ z.2.1.1 z.2.2) b₂ b₃ b₄ =
        C (realRO p₁ Hb (withP y.1 p₁) y.2 z.2.1.1 z.2.2.1 (shOf z.2.2.2 z.1)) z.2.2 z.1 := by
      intro z
      refine (viewOf_agree G s z.1 z.1 (realB Hb p₁ z.2.1.1 z.2.2)
        (givenB p₁ (realRO p₁ Hb (withP y.1 p₁) y.2 z.2.1.1 z.2.2.1 (shOf z.2.2.2 z.1)) z.2.2) b₂ b₂ b₃ b₃ b₄ b₄
        ⟨fun sw hsw => ?_, rfl⟩ (Beh.Agree.refl _ _ _) (Beh.Agree.refl _ _ _) (Beh.Agree.refl _ _ _)).symm
      have : sw ∈ G.σ₁ s := hsw
      rw [hy] at this; cases this; rfl
    have eS : ∀ z : USh × KS p₁, viewOf G s z.1 (simB Hb p₁ z.2.1.2 z.2.2) b₂ b₃ b₄ =
        C (simulate p₁ z.2.1.2)
          (z.2.2.1, (progRO p₁ Hb (withP y.1 p₁) z.2.1.2 (shOf z.2.2.2 z.1)).1) z.1 := by
      intro z
      refine (viewOf_agree G s z.1 z.1 (simB Hb p₁ z.2.1.2 z.2.2)
        (givenB p₁ (simulate p₁ z.2.1.2)
          (z.2.2.1, (progRO p₁ Hb (withP y.1 p₁) z.2.1.2 (shOf z.2.2.2 z.1)).1)) b₂ b₂ b₃ b₃ b₄ b₄
        ⟨fun sw hsw => rfl, ?_⟩ (Beh.Agree.refl _ _ _) (Beh.Agree.refl _ _ _) (Beh.Agree.refl _ _ _)).symm
      show _ = simVis Hb p₁ z.2.1.2 z.2.2 (G.σ₁ s) z.1
      rw [hy]; rfl
    have key := ctx_hop Hb hm hp hHb y (hv.v₁ s y hy) Ψ R5 C
      (fun o V u => traceK5 G (givenB p₁ o V) b₂ b₃ b₄ (C o V u))
      (fun o V u => traceKE G (givenB p₁ o V) b₂ b₃ b₄ (C o V u)) (fun _ _ _ => rfl)
      (fun o V u G5 h => viewOf_G5 G s u (givenB_ok o V) k₂ k₃ k₄ G5 h)
      (fun o V u E h => viewOf_E G s u (givenB_ok o V) k₂ k₃ k₄ E h)
      (fun o V u => card_traceKE G (givenB_ok o V) k₂ k₃ k₄ _)
      GView.with3₁ (fun v => v.v₁.1) (fun o G3 G3' G2 u => ⟨rfl, rfl⟩) hΨ.h5 hΨ.hE hΨ.h3₁
    simp only [eR, eS]
    refine key.trans (add_le_add le_rfl (pr_mono fun z hz => ?_))
    have eP := progRO_fst Hb (withP y.1 p₁) z.2.1.2 (shOf z.2.2.2 z.1)
    rw [eP]
    unfold mainPredIC mainPred2 at hz
    set v := C (simulate p₁ z.2.1.2) (z.2.2.1, @simTab (icPrg z.1.2) Hb CrtGen.tables
      (withP y.1 p₁) z.1.1 (simulate p₁ z.2.1.2) z.2.1.2.1.2.1 z.2.2.2) z.1 with hvdef
    set V' : VP p₁ := (z.2.2.1, @simTab (icPrg z.1.2) Hb CrtGen.tables
      (withP y.1 p₁) z.1.1 (simulate p₁ z.2.1.2) z.2.1.2.1.2.1 z.2.2.2) with hV'
    have hz' : (letI : HasPrg := icPrg z.1.2
        wPre y.2 ∈ candidatesG Hb CrtGen.tables (withP y.1 p₁) enc5 hm
        (R5 v ∪ traceK5 G (givenB p₁ (simulate p₁ z.2.1.2) V') b₂ b₃ b₄ v)
        z.2.1.2.1 z.2.1.2.2) := hz
    have hs : v.s = s := rfl
    have hy' : G.σ₁ v.s = some y := hy
    have ho : v.o₁ = some (simulate p₁ z.2.1.2) := by
      show (G.σ₁ s).map _ = _
      rw [hy]; rfl
    have hT : ∀ k ∈ traceK5 G (givenB p₁ (simulate p₁ z.2.1.2) V') b₂ b₃ b₄ v,
        slotErr v.o₂ ∨ slotErr v.o₃ ∨ slotErr v.o₄ ∨
          k ∈ slotKeys Hb p₂ (yv₂ G v) v.o₂ v.u.2 ∪ slotKeys Hb p₃ (yv₃ G v) v.o₃ v.u.2 ∪ slotKeys Hb p₄ (yv₄ G v) v.o₄ v.u.2 := by
      intro k hk
      unfold traceK5 at hk
      simp only [mem_union] at hk ⊢
      rcases hk with ((hk | hk) | hk) | hk
      · simp [givenB] at hk
      · rcases cov_view k₂ c₂ (yv₂ G v) (hv.v₂ _ _) v.u hk with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h))))
      · rcases cov_view k₃ c₃ (yv₃ G v) (hv.v₃ _ _ _) v.u hk with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr h))))
      · rcases cov_view k₄ c₄ (yv₄ G v) (hv.v₄ _ _ _ _) v.u hk with h | h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    show bstarCore Hb G v.s v.o₁ v.o₂ v.o₃ v.o₄ v.u.2 (R5 v)
    rcases @pred_imp Hb (icPrg z.1.2) p₁ hm y z.2.1.2 _ hz' with h | h | h
    · exact Or.inl (Or.inl (ho ▸ h))
    · refine Or.inr (Or.inl (Or.inl ?_))
      rw [hy', ho]; exact h
    · have h' : ∃ k ∈ R5 v ∪ traceK5 G (givenB p₁ (simulate p₁ z.2.1.2) V') b₂ b₃ b₄ v,
          slotHit Hb p₁ (G.σ₁ v.s) v.o₁ v.u.2 k := by
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
/-- **Replacing the second proof** (the earlier outputs do not depend on the shared tables). -/
theorem hop₂ (hm : MainP p₂) (hp : SmallParams p₂) (hHb : HashesWF Hb)
    (hv : GValid G p₁ p₂ p₃ p₄) (Ψ : GView S p₁ p₂ p₃ p₄ → Prop)
    (R5 : GView S p₁ p₂ p₃ p₄ → Finset (Bytes 37)) {q3 qE : ℕ} (hΨ : Rd Ψ R5 q3 qE) (s : S)
    (b₁ : Beh p₁) (b₃ : Beh p₃) (b₄ : Beh p₄) (k₁ : b₁.OK) (k₃ : b₃.OK) (k₄ : b₄.OK)
    (c₁ : b₁.Cov Hb) (c₃ : b₃.Cov Hb) (c₄ : b₄.Cov Hb) (oa : Option Out)
    (ho₁ : ∀ u, (G.σ₁ s).map (b₁.run · u) = oa) :
    |pr (USh × KS p₂) (fun z => Ψ (viewOf G s z.1 b₁ (realB Hb p₂ z.2.1.1 z.2.2) b₃ b₄)) -
      pr (USh × KS p₂) (fun z => Ψ (viewOf G s z.1 b₁ (simB Hb p₂ z.2.1.2 z.2.2) b₃ b₄))| ≤
      εS q3 (qE + 4 * 4607) + pr (USh × KS p₂) (fun z =>
        bstar Hb G R5 (viewOf G s z.1 b₁ (simB Hb p₂ z.2.1.2 z.2.2) b₃ b₄)) := by
  classical
  rcases hy : G.σ₂ s oa with _ | y
  · have e : ∀ z : USh × KS p₂, viewOf G s z.1 b₁ (simB Hb p₂ z.2.1.2 z.2.2) b₃ b₄ =
        viewOf G s z.1 b₁ (realB Hb p₂ z.2.1.1 z.2.2) b₃ b₄ := by
      intro z
      refine viewOf_agree G s z.1 z.1 b₁ b₁ (realB Hb p₂ z.2.1.1 z.2.2)
        (simB Hb p₂ z.2.1.2 z.2.2) b₃ b₃ b₄ b₄
        (Beh.Agree.refl _ _ _) ⟨fun sw hsw => ?_, ?_⟩ (Beh.Agree.refl _ _ _) (Beh.Agree.refl _ _ _)
      · have : sw ∈ G.σ₂ s ((G.σ₁ s).map (b₁.run · z.1)) := hsw
        rw [ho₁ z.1, hy] at this; cases this
      · show simVis Hb p₂ z.2.1.2 z.2.2 (G.σ₂ s ((G.σ₁ s).map (b₁.run · z.1))) z.1 = z.2.2
        rw [ho₁ z.1, hy]; rfl
    simp only [e, sub_self, abs_zero]
    exact add_nonneg (εS_nonneg _ _) (pr_nonneg _)
  · set C : Out → VP p₂ → USh → GView S p₁ p₂ p₃ p₄ :=
      fun o V u => viewOf G s u b₁ (givenB p₂ o V) b₃ b₄ with hC
    have eR : ∀ z : USh × KS p₂, viewOf G s z.1 b₁ (realB Hb p₂ z.2.1.1 z.2.2) b₃ b₄ =
        C (realRO p₂ Hb (withP y.1 p₂) y.2 z.2.1.1 z.2.2.1 (shOf z.2.2.2 z.1)) z.2.2 z.1 := by
      intro z
      refine (viewOf_agree G s z.1 z.1 b₁ b₁ (realB Hb p₂ z.2.1.1 z.2.2)
        (givenB p₂ (realRO p₂ Hb (withP y.1 p₂) y.2 z.2.1.1 z.2.2.1 (shOf z.2.2.2 z.1)) z.2.2) b₃ b₃ b₄ b₄
        (Beh.Agree.refl _ _ _) ⟨fun sw hsw => ?_, rfl⟩ (Beh.Agree.refl _ _ _) (Beh.Agree.refl _ _ _)).symm
      have : sw ∈ G.σ₂ s ((G.σ₁ s).map (b₁.run · z.1)) := hsw
      rw [ho₁ z.1, hy] at this; cases this; rfl
    have eS : ∀ z : USh × KS p₂, viewOf G s z.1 b₁ (simB Hb p₂ z.2.1.2 z.2.2) b₃ b₄ =
        C (simulate p₂ z.2.1.2)
          (z.2.2.1, (progRO p₂ Hb (withP y.1 p₂) z.2.1.2 (shOf z.2.2.2 z.1)).1) z.1 := by
      intro z
      refine (viewOf_agree G s z.1 z.1 b₁ b₁ (simB Hb p₂ z.2.1.2 z.2.2)
        (givenB p₂ (simulate p₂ z.2.1.2)
          (z.2.2.1, (progRO p₂ Hb (withP y.1 p₂) z.2.1.2 (shOf z.2.2.2 z.1)).1)) b₃ b₃ b₄ b₄
        (Beh.Agree.refl _ _ _) ⟨fun sw hsw => rfl, ?_⟩ (Beh.Agree.refl _ _ _) (Beh.Agree.refl _ _ _)).symm
      show _ = simVis Hb p₂ z.2.1.2 z.2.2 (G.σ₂ s ((G.σ₁ s).map (b₁.run · z.1))) z.1
      rw [ho₁ z.1, hy]; rfl
    have key := ctx_hop Hb hm hp hHb y (hv.v₂ s oa y hy) Ψ R5 C
      (fun o V u => traceK5 G b₁ (givenB p₂ o V) b₃ b₄ (C o V u))
      (fun o V u => traceKE G b₁ (givenB p₂ o V) b₃ b₄ (C o V u)) (fun _ _ _ => rfl)
      (fun o V u G5 h => viewOf_G5 G s u k₁ (givenB_ok o V) k₃ k₄ G5 h)
      (fun o V u E h => viewOf_E G s u k₁ (givenB_ok o V) k₃ k₄ E h)
      (fun o V u => card_traceKE G k₁ (givenB_ok o V) k₃ k₄ _)
      GView.with3₂ (fun v => v.v₂.1) (fun o G3 G3' G2 u => ⟨rfl, rfl⟩) hΨ.h5 hΨ.hE hΨ.h3₂
    simp only [eR, eS]
    refine key.trans (add_le_add le_rfl (pr_mono fun z hz => ?_))
    have eP := progRO_fst Hb (withP y.1 p₂) z.2.1.2 (shOf z.2.2.2 z.1)
    rw [eP]
    unfold mainPredIC mainPred2 at hz
    set v := C (simulate p₂ z.2.1.2) (z.2.2.1, @simTab (icPrg z.1.2) Hb CrtGen.tables
      (withP y.1 p₂) z.1.1 (simulate p₂ z.2.1.2) z.2.1.2.1.2.1 z.2.2.2) z.1 with hvdef
    set V' : VP p₂ := (z.2.2.1, @simTab (icPrg z.1.2) Hb CrtGen.tables
      (withP y.1 p₂) z.1.1 (simulate p₂ z.2.1.2) z.2.1.2.1.2.1 z.2.2.2) with hV'
    have hz' : (letI : HasPrg := icPrg z.1.2
        wPre y.2 ∈ candidatesG Hb CrtGen.tables (withP y.1 p₂) enc5 hm
        (R5 v ∪ traceK5 G b₁ (givenB p₂ (simulate p₂ z.2.1.2) V') b₃ b₄ v)
        z.2.1.2.1 z.2.1.2.2) := hz
    have hs : v.s = s := rfl
    have hy' : G.σ₂ v.s v.o₁ = some y := by
      show G.σ₂ s ((G.σ₁ s).map (b₁.run · z.1)) = _
      rw [ho₁ z.1, hy]
    have ho : v.o₂ = some (simulate p₂ z.2.1.2) := by
      show (G.σ₂ s ((G.σ₁ s).map (b₁.run · z.1))).map _ = _
      rw [ho₁ z.1, hy]; rfl
    have hT : ∀ k ∈ traceK5 G b₁ (givenB p₂ (simulate p₂ z.2.1.2) V') b₃ b₄ v,
        slotErr v.o₁ ∨ slotErr v.o₃ ∨ slotErr v.o₄ ∨
          k ∈ slotKeys Hb p₁ (yv₁ G v) v.o₁ v.u.2 ∪ slotKeys Hb p₃ (yv₃ G v) v.o₃ v.u.2 ∪ slotKeys Hb p₄ (yv₄ G v) v.o₄ v.u.2 := by
      intro k hk
      unfold traceK5 at hk
      simp only [mem_union] at hk ⊢
      rcases hk with ((hk | hk) | hk) | hk
      · rcases cov_view k₁ c₁ (yv₁ G v) (hv.v₁ _) v.u hk with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h))))
      · simp [givenB] at hk
      · rcases cov_view k₃ c₃ (yv₃ G v) (hv.v₃ _ _ _) v.u hk with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr h))))
      · rcases cov_view k₄ c₄ (yv₄ G v) (hv.v₄ _ _ _ _) v.u hk with h | h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    show bstarCore Hb G v.s v.o₁ v.o₂ v.o₃ v.o₄ v.u.2 (R5 v)
    rcases @pred_imp Hb (icPrg z.1.2) p₂ hm y z.2.1.2 _ hz' with h | h | h
    · exact Or.inl (Or.inr (Or.inl (ho ▸ h)))
    · refine Or.inr (Or.inr (Or.inl (Or.inl ?_)))
      rw [hy', ho]; exact h
    · have h' : ∃ k ∈ R5 v ∪ traceK5 G b₁ (givenB p₂ (simulate p₂ z.2.1.2) V') b₃ b₄ v,
          slotHit Hb p₂ (G.σ₂ v.s v.o₁) v.o₂ v.u.2 k := by
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
/-- **Replacing the third proof** (the earlier outputs do not depend on the shared tables). -/
theorem hop₃ (hm : MainP p₃) (hp : SmallParams p₃) (hHb : HashesWF Hb)
    (hv : GValid G p₁ p₂ p₃ p₄) (Ψ : GView S p₁ p₂ p₃ p₄ → Prop)
    (R5 : GView S p₁ p₂ p₃ p₄ → Finset (Bytes 37)) {q3 qE : ℕ} (hΨ : Rd Ψ R5 q3 qE) (s : S)
    (b₁ : Beh p₁) (b₂ : Beh p₂) (b₄ : Beh p₄) (k₁ : b₁.OK) (k₂ : b₂.OK) (k₄ : b₄.OK)
    (c₁ : b₁.Cov Hb) (c₂ : b₂.Cov Hb) (c₄ : b₄.Cov Hb) (oa : Option Out) (ob : Option Out)
    (ho₁ : ∀ u, (G.σ₁ s).map (b₁.run · u) = oa)
    (ho₂ : ∀ u, (G.σ₂ s oa).map (b₂.run · u) = ob) :
    |pr (USh × KS p₃) (fun z => Ψ (viewOf G s z.1 b₁ b₂ (realB Hb p₃ z.2.1.1 z.2.2) b₄)) -
      pr (USh × KS p₃) (fun z => Ψ (viewOf G s z.1 b₁ b₂ (simB Hb p₃ z.2.1.2 z.2.2) b₄))| ≤
      εS q3 (qE + 4 * 4607) + pr (USh × KS p₃) (fun z =>
        bstar Hb G R5 (viewOf G s z.1 b₁ b₂ (simB Hb p₃ z.2.1.2 z.2.2) b₄)) := by
  classical
  rcases hy : G.σ₃ s oa ob with _ | y
  · have e : ∀ z : USh × KS p₃, viewOf G s z.1 b₁ b₂ (simB Hb p₃ z.2.1.2 z.2.2) b₄ =
        viewOf G s z.1 b₁ b₂ (realB Hb p₃ z.2.1.1 z.2.2) b₄ := by
      intro z
      refine viewOf_agree G s z.1 z.1 b₁ b₁ b₂ b₂ (realB Hb p₃ z.2.1.1 z.2.2)
        (simB Hb p₃ z.2.1.2 z.2.2) b₄ b₄
        (Beh.Agree.refl _ _ _) (Beh.Agree.refl _ _ _) ⟨fun sw hsw => ?_, ?_⟩ (Beh.Agree.refl _ _ _)
      · have : sw ∈ G.σ₃ s ((G.σ₁ s).map (b₁.run · z.1)) ((G.σ₂ s ((G.σ₁ s).map (b₁.run · z.1))).map (b₂.run · z.1)) := hsw
        rw [ho₁ z.1, ho₂ z.1, hy] at this; cases this
      · show simVis Hb p₃ z.2.1.2 z.2.2 (G.σ₃ s ((G.σ₁ s).map (b₁.run · z.1)) ((G.σ₂ s ((G.σ₁ s).map (b₁.run · z.1))).map (b₂.run · z.1))) z.1 = z.2.2
        rw [ho₁ z.1, ho₂ z.1, hy]; rfl
    simp only [e, sub_self, abs_zero]
    exact add_nonneg (εS_nonneg _ _) (pr_nonneg _)
  · set C : Out → VP p₃ → USh → GView S p₁ p₂ p₃ p₄ :=
      fun o V u => viewOf G s u b₁ b₂ (givenB p₃ o V) b₄ with hC
    have eR : ∀ z : USh × KS p₃, viewOf G s z.1 b₁ b₂ (realB Hb p₃ z.2.1.1 z.2.2) b₄ =
        C (realRO p₃ Hb (withP y.1 p₃) y.2 z.2.1.1 z.2.2.1 (shOf z.2.2.2 z.1)) z.2.2 z.1 := by
      intro z
      refine (viewOf_agree G s z.1 z.1 b₁ b₁ b₂ b₂ (realB Hb p₃ z.2.1.1 z.2.2)
        (givenB p₃ (realRO p₃ Hb (withP y.1 p₃) y.2 z.2.1.1 z.2.2.1 (shOf z.2.2.2 z.1)) z.2.2) b₄ b₄
        (Beh.Agree.refl _ _ _) (Beh.Agree.refl _ _ _) ⟨fun sw hsw => ?_, rfl⟩ (Beh.Agree.refl _ _ _)).symm
      have : sw ∈ G.σ₃ s ((G.σ₁ s).map (b₁.run · z.1)) ((G.σ₂ s ((G.σ₁ s).map (b₁.run · z.1))).map (b₂.run · z.1)) := hsw
      rw [ho₁ z.1, ho₂ z.1, hy] at this; cases this; rfl
    have eS : ∀ z : USh × KS p₃, viewOf G s z.1 b₁ b₂ (simB Hb p₃ z.2.1.2 z.2.2) b₄ =
        C (simulate p₃ z.2.1.2)
          (z.2.2.1, (progRO p₃ Hb (withP y.1 p₃) z.2.1.2 (shOf z.2.2.2 z.1)).1) z.1 := by
      intro z
      refine (viewOf_agree G s z.1 z.1 b₁ b₁ b₂ b₂ (simB Hb p₃ z.2.1.2 z.2.2)
        (givenB p₃ (simulate p₃ z.2.1.2)
          (z.2.2.1, (progRO p₃ Hb (withP y.1 p₃) z.2.1.2 (shOf z.2.2.2 z.1)).1)) b₄ b₄
        (Beh.Agree.refl _ _ _) (Beh.Agree.refl _ _ _) ⟨fun sw hsw => rfl, ?_⟩ (Beh.Agree.refl _ _ _)).symm
      show _ = simVis Hb p₃ z.2.1.2 z.2.2 (G.σ₃ s ((G.σ₁ s).map (b₁.run · z.1)) ((G.σ₂ s ((G.σ₁ s).map (b₁.run · z.1))).map (b₂.run · z.1))) z.1
      rw [ho₁ z.1, ho₂ z.1, hy]; rfl
    have key := ctx_hop Hb hm hp hHb y (hv.v₃ s oa ob y hy) Ψ R5 C
      (fun o V u => traceK5 G b₁ b₂ (givenB p₃ o V) b₄ (C o V u))
      (fun o V u => traceKE G b₁ b₂ (givenB p₃ o V) b₄ (C o V u)) (fun _ _ _ => rfl)
      (fun o V u G5 h => viewOf_G5 G s u k₁ k₂ (givenB_ok o V) k₄ G5 h)
      (fun o V u E h => viewOf_E G s u k₁ k₂ (givenB_ok o V) k₄ E h)
      (fun o V u => card_traceKE G k₁ k₂ (givenB_ok o V) k₄ _)
      GView.with3₃ (fun v => v.v₃.1) (fun o G3 G3' G2 u => ⟨rfl, rfl⟩) hΨ.h5 hΨ.hE hΨ.h3₃
    simp only [eR, eS]
    refine key.trans (add_le_add le_rfl (pr_mono fun z hz => ?_))
    have eP := progRO_fst Hb (withP y.1 p₃) z.2.1.2 (shOf z.2.2.2 z.1)
    rw [eP]
    unfold mainPredIC mainPred2 at hz
    set v := C (simulate p₃ z.2.1.2) (z.2.2.1, @simTab (icPrg z.1.2) Hb CrtGen.tables
      (withP y.1 p₃) z.1.1 (simulate p₃ z.2.1.2) z.2.1.2.1.2.1 z.2.2.2) z.1 with hvdef
    set V' : VP p₃ := (z.2.2.1, @simTab (icPrg z.1.2) Hb CrtGen.tables
      (withP y.1 p₃) z.1.1 (simulate p₃ z.2.1.2) z.2.1.2.1.2.1 z.2.2.2) with hV'
    have hz' : (letI : HasPrg := icPrg z.1.2
        wPre y.2 ∈ candidatesG Hb CrtGen.tables (withP y.1 p₃) enc5 hm
        (R5 v ∪ traceK5 G b₁ b₂ (givenB p₃ (simulate p₃ z.2.1.2) V') b₄ v)
        z.2.1.2.1 z.2.1.2.2) := hz
    have hs : v.s = s := rfl
    have hy' : G.σ₃ v.s v.o₁ v.o₂ = some y := by
      show G.σ₃ s ((G.σ₁ s).map (b₁.run · z.1)) ((G.σ₂ s ((G.σ₁ s).map (b₁.run · z.1))).map (b₂.run · z.1)) = _
      rw [ho₁ z.1, ho₂ z.1, hy]
    have ho : v.o₃ = some (simulate p₃ z.2.1.2) := by
      show (G.σ₃ s ((G.σ₁ s).map (b₁.run · z.1)) ((G.σ₂ s ((G.σ₁ s).map (b₁.run · z.1))).map (b₂.run · z.1))).map _ = _
      rw [ho₁ z.1, ho₂ z.1, hy]; rfl
    have hT : ∀ k ∈ traceK5 G b₁ b₂ (givenB p₃ (simulate p₃ z.2.1.2) V') b₄ v,
        slotErr v.o₁ ∨ slotErr v.o₂ ∨ slotErr v.o₄ ∨
          k ∈ slotKeys Hb p₁ (yv₁ G v) v.o₁ v.u.2 ∪ slotKeys Hb p₂ (yv₂ G v) v.o₂ v.u.2 ∪ slotKeys Hb p₄ (yv₄ G v) v.o₄ v.u.2 := by
      intro k hk
      unfold traceK5 at hk
      simp only [mem_union] at hk ⊢
      rcases hk with ((hk | hk) | hk) | hk
      · rcases cov_view k₁ c₁ (yv₁ G v) (hv.v₁ _) v.u hk with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h))))
      · rcases cov_view k₂ c₂ (yv₂ G v) (hv.v₂ _ _) v.u hk with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr h))))
      · simp [givenB] at hk
      · rcases cov_view k₄ c₄ (yv₄ G v) (hv.v₄ _ _ _ _) v.u hk with h | h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    show bstarCore Hb G v.s v.o₁ v.o₂ v.o₃ v.o₄ v.u.2 (R5 v)
    rcases @pred_imp Hb (icPrg z.1.2) p₃ hm y z.2.1.2 _ hz' with h | h | h
    · exact Or.inl (Or.inr (Or.inr (Or.inl (ho ▸ h))))
    · refine Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ?_))))
      rw [hy', ho]; exact h
    · have h' : ∃ k ∈ R5 v ∪ traceK5 G b₁ b₂ (givenB p₃ (simulate p₃ z.2.1.2) V') b₄ v,
          slotHit Hb p₃ (G.σ₃ v.s v.o₁ v.o₂) v.o₃ v.u.2 k := by
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
/-- **Replacing the fourth proof** (the earlier outputs do not depend on the shared tables). -/
theorem hop₄ (hm : MainP p₄) (hp : SmallParams p₄) (hHb : HashesWF Hb)
    (hv : GValid G p₁ p₂ p₃ p₄) (Ψ : GView S p₁ p₂ p₃ p₄ → Prop)
    (R5 : GView S p₁ p₂ p₃ p₄ → Finset (Bytes 37)) {q3 qE : ℕ} (hΨ : Rd Ψ R5 q3 qE) (s : S)
    (b₁ : Beh p₁) (b₂ : Beh p₂) (b₃ : Beh p₃) (k₁ : b₁.OK) (k₂ : b₂.OK) (k₃ : b₃.OK)
    (c₁ : b₁.Cov Hb) (c₂ : b₂.Cov Hb) (c₃ : b₃.Cov Hb) (oa : Option Out) (ob : Option Out) (oc : Option Out)
    (ho₁ : ∀ u, (G.σ₁ s).map (b₁.run · u) = oa)
    (ho₂ : ∀ u, (G.σ₂ s oa).map (b₂.run · u) = ob)
    (ho₃ : ∀ u, (G.σ₃ s oa ob).map (b₃.run · u) = oc) :
    |pr (USh × KS p₄) (fun z => Ψ (viewOf G s z.1 b₁ b₂ b₃ (realB Hb p₄ z.2.1.1 z.2.2))) -
      pr (USh × KS p₄) (fun z => Ψ (viewOf G s z.1 b₁ b₂ b₃ (simB Hb p₄ z.2.1.2 z.2.2)))| ≤
      εS q3 (qE + 4 * 4607) + pr (USh × KS p₄) (fun z =>
        bstar Hb G R5 (viewOf G s z.1 b₁ b₂ b₃ (simB Hb p₄ z.2.1.2 z.2.2))) := by
  classical
  rcases hy : G.σ₄ s oa ob oc with _ | y
  · have e : ∀ z : USh × KS p₄, viewOf G s z.1 b₁ b₂ b₃ (simB Hb p₄ z.2.1.2 z.2.2) =
        viewOf G s z.1 b₁ b₂ b₃ (realB Hb p₄ z.2.1.1 z.2.2) := by
      intro z
      refine viewOf_agree G s z.1 z.1 b₁ b₁ b₂ b₂ b₃ b₃ (realB Hb p₄ z.2.1.1 z.2.2)
        (simB Hb p₄ z.2.1.2 z.2.2)
        (Beh.Agree.refl _ _ _) (Beh.Agree.refl _ _ _) (Beh.Agree.refl _ _ _) ⟨fun sw hsw => ?_, ?_⟩
      · have : sw ∈ G.σ₄ s ((G.σ₁ s).map (b₁.run · z.1)) ((G.σ₂ s ((G.σ₁ s).map (b₁.run · z.1))).map (b₂.run · z.1)) ((G.σ₃ s ((G.σ₁ s).map (b₁.run · z.1)) ((G.σ₂ s ((G.σ₁ s).map (b₁.run · z.1))).map (b₂.run · z.1))).map (b₃.run · z.1)) := hsw
        rw [ho₁ z.1, ho₂ z.1, ho₃ z.1, hy] at this; cases this
      · show simVis Hb p₄ z.2.1.2 z.2.2 (G.σ₄ s ((G.σ₁ s).map (b₁.run · z.1)) ((G.σ₂ s ((G.σ₁ s).map (b₁.run · z.1))).map (b₂.run · z.1)) ((G.σ₃ s ((G.σ₁ s).map (b₁.run · z.1)) ((G.σ₂ s ((G.σ₁ s).map (b₁.run · z.1))).map (b₂.run · z.1))).map (b₃.run · z.1))) z.1 = z.2.2
        rw [ho₁ z.1, ho₂ z.1, ho₃ z.1, hy]; rfl
    simp only [e, sub_self, abs_zero]
    exact add_nonneg (εS_nonneg _ _) (pr_nonneg _)
  · set C : Out → VP p₄ → USh → GView S p₁ p₂ p₃ p₄ :=
      fun o V u => viewOf G s u b₁ b₂ b₃ (givenB p₄ o V) with hC
    have eR : ∀ z : USh × KS p₄, viewOf G s z.1 b₁ b₂ b₃ (realB Hb p₄ z.2.1.1 z.2.2) =
        C (realRO p₄ Hb (withP y.1 p₄) y.2 z.2.1.1 z.2.2.1 (shOf z.2.2.2 z.1)) z.2.2 z.1 := by
      intro z
      refine (viewOf_agree G s z.1 z.1 b₁ b₁ b₂ b₂ b₃ b₃ (realB Hb p₄ z.2.1.1 z.2.2)
        (givenB p₄ (realRO p₄ Hb (withP y.1 p₄) y.2 z.2.1.1 z.2.2.1 (shOf z.2.2.2 z.1)) z.2.2)
        (Beh.Agree.refl _ _ _) (Beh.Agree.refl _ _ _) (Beh.Agree.refl _ _ _) ⟨fun sw hsw => ?_, rfl⟩).symm
      have : sw ∈ G.σ₄ s ((G.σ₁ s).map (b₁.run · z.1)) ((G.σ₂ s ((G.σ₁ s).map (b₁.run · z.1))).map (b₂.run · z.1)) ((G.σ₃ s ((G.σ₁ s).map (b₁.run · z.1)) ((G.σ₂ s ((G.σ₁ s).map (b₁.run · z.1))).map (b₂.run · z.1))).map (b₃.run · z.1)) := hsw
      rw [ho₁ z.1, ho₂ z.1, ho₃ z.1, hy] at this; cases this; rfl
    have eS : ∀ z : USh × KS p₄, viewOf G s z.1 b₁ b₂ b₃ (simB Hb p₄ z.2.1.2 z.2.2) =
        C (simulate p₄ z.2.1.2)
          (z.2.2.1, (progRO p₄ Hb (withP y.1 p₄) z.2.1.2 (shOf z.2.2.2 z.1)).1) z.1 := by
      intro z
      refine (viewOf_agree G s z.1 z.1 b₁ b₁ b₂ b₂ b₃ b₃ (simB Hb p₄ z.2.1.2 z.2.2)
        (givenB p₄ (simulate p₄ z.2.1.2)
          (z.2.2.1, (progRO p₄ Hb (withP y.1 p₄) z.2.1.2 (shOf z.2.2.2 z.1)).1))
        (Beh.Agree.refl _ _ _) (Beh.Agree.refl _ _ _) (Beh.Agree.refl _ _ _) ⟨fun sw hsw => rfl, ?_⟩).symm
      show _ = simVis Hb p₄ z.2.1.2 z.2.2 (G.σ₄ s ((G.σ₁ s).map (b₁.run · z.1)) ((G.σ₂ s ((G.σ₁ s).map (b₁.run · z.1))).map (b₂.run · z.1)) ((G.σ₃ s ((G.σ₁ s).map (b₁.run · z.1)) ((G.σ₂ s ((G.σ₁ s).map (b₁.run · z.1))).map (b₂.run · z.1))).map (b₃.run · z.1))) z.1
      rw [ho₁ z.1, ho₂ z.1, ho₃ z.1, hy]; rfl
    have key := ctx_hop Hb hm hp hHb y (hv.v₄ s oa ob oc y hy) Ψ R5 C
      (fun o V u => traceK5 G b₁ b₂ b₃ (givenB p₄ o V) (C o V u))
      (fun o V u => traceKE G b₁ b₂ b₃ (givenB p₄ o V) (C o V u)) (fun _ _ _ => rfl)
      (fun o V u G5 h => viewOf_G5 G s u k₁ k₂ k₃ (givenB_ok o V) G5 h)
      (fun o V u E h => viewOf_E G s u k₁ k₂ k₃ (givenB_ok o V) E h)
      (fun o V u => card_traceKE G k₁ k₂ k₃ (givenB_ok o V) _)
      GView.with3₄ (fun v => v.v₄.1) (fun o G3 G3' G2 u => ⟨rfl, rfl⟩) hΨ.h5 hΨ.hE hΨ.h3₄
    simp only [eR, eS]
    refine key.trans (add_le_add le_rfl (pr_mono fun z hz => ?_))
    have eP := progRO_fst Hb (withP y.1 p₄) z.2.1.2 (shOf z.2.2.2 z.1)
    rw [eP]
    unfold mainPredIC mainPred2 at hz
    set v := C (simulate p₄ z.2.1.2) (z.2.2.1, @simTab (icPrg z.1.2) Hb CrtGen.tables
      (withP y.1 p₄) z.1.1 (simulate p₄ z.2.1.2) z.2.1.2.1.2.1 z.2.2.2) z.1 with hvdef
    set V' : VP p₄ := (z.2.2.1, @simTab (icPrg z.1.2) Hb CrtGen.tables
      (withP y.1 p₄) z.1.1 (simulate p₄ z.2.1.2) z.2.1.2.1.2.1 z.2.2.2) with hV'
    have hz' : (letI : HasPrg := icPrg z.1.2
        wPre y.2 ∈ candidatesG Hb CrtGen.tables (withP y.1 p₄) enc5 hm
        (R5 v ∪ traceK5 G b₁ b₂ b₃ (givenB p₄ (simulate p₄ z.2.1.2) V') v)
        z.2.1.2.1 z.2.1.2.2) := hz
    have hs : v.s = s := rfl
    have hy' : G.σ₄ v.s v.o₁ v.o₂ v.o₃ = some y := by
      show G.σ₄ s ((G.σ₁ s).map (b₁.run · z.1)) ((G.σ₂ s ((G.σ₁ s).map (b₁.run · z.1))).map (b₂.run · z.1)) ((G.σ₃ s ((G.σ₁ s).map (b₁.run · z.1)) ((G.σ₂ s ((G.σ₁ s).map (b₁.run · z.1))).map (b₂.run · z.1))).map (b₃.run · z.1)) = _
      rw [ho₁ z.1, ho₂ z.1, ho₃ z.1, hy]
    have ho : v.o₄ = some (simulate p₄ z.2.1.2) := by
      show (G.σ₄ s ((G.σ₁ s).map (b₁.run · z.1)) ((G.σ₂ s ((G.σ₁ s).map (b₁.run · z.1))).map (b₂.run · z.1)) ((G.σ₃ s ((G.σ₁ s).map (b₁.run · z.1)) ((G.σ₂ s ((G.σ₁ s).map (b₁.run · z.1))).map (b₂.run · z.1))).map (b₃.run · z.1))).map _ = _
      rw [ho₁ z.1, ho₂ z.1, ho₃ z.1, hy]; rfl
    have hT : ∀ k ∈ traceK5 G b₁ b₂ b₃ (givenB p₄ (simulate p₄ z.2.1.2) V') v,
        slotErr v.o₁ ∨ slotErr v.o₂ ∨ slotErr v.o₃ ∨
          k ∈ slotKeys Hb p₁ (yv₁ G v) v.o₁ v.u.2 ∪ slotKeys Hb p₂ (yv₂ G v) v.o₂ v.u.2 ∪ slotKeys Hb p₃ (yv₃ G v) v.o₃ v.u.2 := by
      intro k hk
      unfold traceK5 at hk
      simp only [mem_union] at hk ⊢
      rcases hk with ((hk | hk) | hk) | hk
      · rcases cov_view k₁ c₁ (yv₁ G v) (hv.v₁ _) v.u hk with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h))))
      · rcases cov_view k₂ c₂ (yv₂ G v) (hv.v₂ _ _) v.u hk with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr h))))
      · rcases cov_view k₃ c₃ (yv₃ G v) (hv.v₃ _ _ _) v.u hk with h | h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · simp [givenB] at hk
    show bstarCore Hb G v.s v.o₁ v.o₂ v.o₃ v.o₄ v.u.2 (R5 v)
    rcases @pred_imp Hb (icPrg z.1.2) p₄ hm y z.2.1.2 _ hz' with h | h | h
    · exact Or.inl (Or.inr (Or.inr (Or.inr (ho ▸ h))))
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
      rw [hy', ho]; exact h
    · have h' : ∃ k ∈ R5 v ∪ traceK5 G b₁ b₂ b₃ (givenB p₄ (simulate p₄ z.2.1.2) V') v,
          slotHit Hb p₄ (G.σ₄ v.s v.o₁ v.o₂ v.o₃) v.o₄ v.u.2 k := by
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

end Hops

end VoleMole.ZK.Sim
