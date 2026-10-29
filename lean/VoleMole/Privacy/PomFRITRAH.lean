import VoleMole.Privacy.PomFRITRAGame
import VoleMole.ZK.CollideAd2

/-!
# PomFRIT blindness with an Issuer whose interaction also reads `H₂³`

`blindnessRA_lean_num` (`Privacy/PomFRITRAGame.lean`) lets the Issuer's key, messages and
responses read the slices, `H₅` and the cipher, but not `H₂³` (`IBudget`: no `H₂³` key). Here they
may read `H₂³` too.

## Why `H₂³` was excluded, and what changes

In the hybrids the two-phase simulator programs `H₂³` (at the block of the prefix it recomputes,
and at the zero-prefix block when its continuation stops), and the reductions see only the
programmed tables. An interaction that reads `H₂³` would then be computed on different tables in
the real and the simulated runs: the stop decision could read the zero block the simulator
overwrites, the continuation could read the block it later programs, and the reduction would
compute the other session's responses on the programmed tables.

None of this is needed here: **the interaction's `H₂³` reads are taken out before the hybrids
start**, by lazy sampling, and the existing theorem is applied to an Issuer that does not read
`H₂³`. No simulator changes.

* *The joint budget* (`IBudgetH i₃ i₂ i₅ i_E`): the key stage and the response stage at every pair
  of requests are consistent readers of **both** slices and the shared tables jointly
  (`SReadsP`), at most `i₃` keys of each slice, `i₂` `H₂³` keys, `i₅` `H₅` keys, `i_E` cipher keys.
  (Per-slice reads, as in `IBudget`, would not do: the guess below must recompute the
  interaction's `H₂³` read set consistently as either slice varies.)
* *Lazy sampling of `H₂³`* (`pr_resampleC`, `G0RA_resample`): with everything else fixed, the
  interaction (key, messages, the responses to the actual requests) reads `H₂³` at a set `Q(Γ)` of
  at most `2·i₂` keys. So the game on `H₂³ = G₂` is the game in which the interaction reads an
  independent table `Γ`, the sessions run on `G₂` patched at `Q(Γ)` with `Γ`, and so does the
  guess. This is the game of the Issuer `A.subst Γ`, whose interaction reads `Γ` in place of
  `H₂³` and whose guess patches the `H₂³` table it sees at the interaction's read set (which it
  recomputes from the requests and the tables), **except** that `A.subst Γ`'s sessions run on the
  unpatched `G₂`: the two differ only if a session's real run reads `H₂³` at a patched key
  (`badH`).
* *The issuer `A.subst Γ`* does not read `H₂³` (`IBudget`, from the joint budget at `Γ`,
  `IBudgetH.subst`), and its guess reads `(q₃ + 2i₃, q₅ + 2i₅, q_E + 2i_E)` keys
  (`GBudget.subst`). `blindnessRA_lean_numG` applies to it for every `Γ`.
* *The collision term* (`badH`): a real session reads `H₂³` only at the grinding points of its
  prefix `pre = chal2 ‖ qs_check ‖ ã` (`realRun2_h23_congr`), so `badH` means that the
  interaction's read set meets the session's grinding block. This is `ZK.Sim.pr_tail2A` for the
  session's two-phase run, with its continuation (`K0`, `K1R`) and the read set (`qf0`, `qf1`) at
  `A.subst Γ`: a second application of two-phase zero knowledge, after which the block's tail is
  the simulator's uniform `ã` (16 bytes), independent of the read set.

**`blindnessRAH_lean_numG`** (every type of cipher rows), **`blindnessRAH_lean_num`** (function
rows):

    |Pr[W₀] − Pr[W₁]| ≤ 4·εz(pP; q₃ + 6i₃, q₅ + 6i₅ + 1872, q_E + 6i_E + 23035)
                         + 2·noHitProb + 2·2⁻¹²⁸ + h23H(i₃, i₂, i₅, i_E),
    h23H = 0 if i₂ = 0, else 4·(2⁻¹¹³ + εz(pP; 6i₃, 6i₅ + 2184, 6i_E + 18428) + 2i₂·2⁻¹²⁸).

The interaction's reads enter the main term six times per hop (twice in the guess of `A.subst Γ`,
which recomputes them, and four times in `blindnessRA`'s hops); for `i₂ = 0`,
`blindnessRA_lean_num` itself (four times) is the better bound. With AES as random
permutations: `blindnessRAH_lean_num_perm` (`Privacy/PermRA.lean`); for an Issuer written as
oracle computations over the tables: `blindnessOCH_lean_num` (`ROM/PrivacyReads.lean`).
-/

open Finset

-- (The coin types are large products: their `Fintype` instances exceed the default size.)
set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.PomFRIT

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.ZK.Sim VoleMole.Arith
open VoleMole.Spec VoleMole.Spec.PomFRIT VoleMole.ZK.IC

-- `Com` and the UOV map evaluate Keccak and the public map; nothing below needs to unfold them.
attribute [local irreducible] commitRefresher UOVKey.eval

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R]

/-! ## Joint readers of both slices and the shared tables -/

section Joint

/-- **The tables of the PomFRIT game**: both slices and the shared tables. -/
abbrev TbP (R : Type) := SlP × ShP R

/-- **Read sets** of the five tables (both slices, `H₂³`, `H₅`, cipher). -/
abbrev RSP := (Finset (Bytes 16) × Finset (Bytes 16)) × (Finset (K2 pP) × (Finset (Bytes 37) × Finset Blk))

/-- `a` and `a'` agree on the read sets `r`. -/
def AgP (r : RSP) (a a' : TbP R) : Prop :=
  (∀ k ∈ r.1.1, a.1.1 k = a'.1.1 k) ∧ (∀ k ∈ r.1.2, a.1.2 k = a'.1.2 k) ∧
    (∀ k ∈ r.2.1, a.2.1 k = a'.2.1 k) ∧ (∀ k ∈ r.2.2.1, a.2.2.1 k = a'.2.2.1 k) ∧
      ∀ k ∈ r.2.2.2, a.2.2.2 k = a'.2.2.2 k

/-- **A consistent reader of both slices and the shared tables** (`SReads` for the pair of
slices): its read sets `Q t` and its output are determined by the tables on `Q t`, at most `a₃`
keys of each slice, `a₂` of `H₂³`, `a₅` of `H₅`, `a_E` of the cipher. -/
def SReadsP {X : Type*} (f : TbP R → X) (a3 a2 a5 aE : ℕ) : Prop :=
  ∃ Q : TbP R → RSP, (∀ t t', AgP (Q t) t t' → Q t' = Q t ∧ f t' = f t) ∧
    ∀ t, (Q t).1.1.card ≤ a3 ∧ (Q t).1.2.card ≤ a3 ∧ (Q t).2.1.card ≤ a2 ∧
      (Q t).2.2.1.card ≤ a5 ∧ (Q t).2.2.2.card ≤ aE

/-- The consistency of explicit read sets `Q` for a reader `f`. -/
def ConsP {X : Type*} (Q : TbP R → RSP) (f : TbP R → X) : Prop :=
  ∀ t t', AgP (Q t) t t' → Q t' = Q t ∧ f t' = f t

/-- The bounds of explicit read sets. -/
def CardP (Q : TbP R → RSP) (a3 a2 a5 aE : ℕ) : Prop :=
  ∀ t, (Q t).1.1.card ≤ a3 ∧ (Q t).1.2.card ≤ a3 ∧ (Q t).2.1.card ≤ a2 ∧
    (Q t).2.2.1.card ≤ a5 ∧ (Q t).2.2.2.card ≤ aE

variable {X : Type*} {Q : TbP R → RSP} {f : TbP R → X}

/-- **Slice `0` alone**, the other slice fixed and `H₂³` replaced by `Γ`: an `SReads` with no
`H₂³` key. -/
lemma ConsP.at0 (hQ : ConsP Q f) {a3 a2 a5 aE : ℕ} (hc : CardP Q a3 a2 a5 aE) (g₁ : Tab3)
    (Γ : Tab2G pP) : SReads pP (fun t : Tb R pP => f ((t.1, g₁), (Γ, t.2.2))) a3 0 a5 aE := by
  refine ⟨fun t => ((Q ((t.1, g₁), (Γ, t.2.2))).1.1, ∅, (Q ((t.1, g₁), (Γ, t.2.2))).2.2.1,
    (Q ((t.1, g₁), (Γ, t.2.2))).2.2.2), fun t t' h => ?_, fun t => ?_⟩
  · obtain ⟨h3, -, h5, hE⟩ := h
    obtain ⟨e1, e2⟩ := hQ ((t.1, g₁), (Γ, t.2.2)) ((t'.1, g₁), (Γ, t'.2.2))
      ⟨h3, fun _ _ => rfl, fun _ _ => rfl, h5, hE⟩
    exact ⟨by simp only [e1], e2⟩
  · obtain ⟨c1, -, -, c4, c5⟩ := hc ((t.1, g₁), (Γ, t.2.2))
    exact ⟨c1, by simp, c4, c5⟩

/-- **Slice `1` alone.** -/
lemma ConsP.at1 (hQ : ConsP Q f) {a3 a2 a5 aE : ℕ} (hc : CardP Q a3 a2 a5 aE) (g₀ : Tab3)
    (Γ : Tab2G pP) : SReads pP (fun t : Tb R pP => f ((g₀, t.1), (Γ, t.2.2))) a3 0 a5 aE := by
  refine ⟨fun t => ((Q ((g₀, t.1), (Γ, t.2.2))).1.2, ∅, (Q ((g₀, t.1), (Γ, t.2.2))).2.2.1,
    (Q ((g₀, t.1), (Γ, t.2.2))).2.2.2), fun t t' h => ?_, fun t => ?_⟩
  · obtain ⟨h3, -, h5, hE⟩ := h
    obtain ⟨e1, e2⟩ := hQ ((g₀, t.1), (Γ, t.2.2)) ((g₀, t'.1), (Γ, t'.2.2))
      ⟨fun _ _ => rfl, h3, fun _ _ => rfl, h5, hE⟩
    exact ⟨by simp only [e1], e2⟩
  · obtain ⟨-, c2, -, c4, c5⟩ := hc ((g₀, t.1), (Γ, t.2.2))
    exact ⟨c2, by simp, c4, c5⟩

/-- The read sets and the output, as a function of slice `0`. -/
lemma ConsP.rd30 (hQ : ConsP Q f) {a3 a2 a5 aE : ℕ} (hc : CardP Q a3 a2 a5 aE) (g₁ : Tab3)
    (s : ShP R) : Rd3 (fun g => (Q ((g, g₁), s), f ((g, g₁), s))) a3 :=
  ⟨fun g => (Q ((g, g₁), s)).1.1, fun g => (hc _).1, fun g g' h => by
    obtain ⟨e1, e2⟩ := hQ ((g, g₁), s) ((g', g₁), s)
      ⟨h, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
    exact Prod.ext e1 e2⟩

/-- The read sets and the output, as a function of slice `1`. -/
lemma ConsP.rd31 (hQ : ConsP Q f) {a3 a2 a5 aE : ℕ} (hc : CardP Q a3 a2 a5 aE) (g₀ : Tab3)
    (s : ShP R) : Rd3 (fun g => (Q ((g₀, g), s), f ((g₀, g), s))) a3 :=
  ⟨fun g => (Q ((g₀, g), s)).1.2, fun g => (hc _).2.1, fun g g' h => by
    obtain ⟨e1, e2⟩ := hQ ((g₀, g), s) ((g₀, g'), s)
      ⟨fun _ _ => rfl, h, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
    exact Prod.ext e1 e2⟩

/-- The read sets and the output at `H₂³ = Γ`, as a function of the shared tables (`H₅`). -/
lemma ConsP.rd5 (hQ : ConsP Q f) {a3 a2 a5 aE : ℕ} (hc : CardP Q a3 a2 a5 aE) (sl : SlP)
    (Γ : Tab2G pP) : Rd5 (fun s : ShP R => (Q (sl, (Γ, s.2)), f (sl, (Γ, s.2)))) a5 :=
  ⟨fun s => (Q (sl, (Γ, s.2))).2.2.1, fun s => (hc _).2.2.2.1, fun s G5 h => by
    obtain ⟨e1, e2⟩ := hQ (sl, (Γ, s.2)) (sl, (Γ, (G5, s.2.2)))
      ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, h, fun _ _ => rfl⟩
    exact Prod.ext e1 e2⟩

/-- The read sets and the output at `H₂³ = Γ`, as a function of the shared tables (cipher). -/
lemma ConsP.rdE (hQ : ConsP Q f) {a3 a2 a5 aE : ℕ} (hc : CardP Q a3 a2 a5 aE) (sl : SlP)
    (Γ : Tab2G pP) : RdE (fun s : ShP R => (Q (sl, (Γ, s.2)), f (sl, (Γ, s.2)))) aE :=
  ⟨fun s => (Q (sl, (Γ, s.2))).2.2.2, fun s => (hc _).2.2.2.2, fun s E h => by
    obtain ⟨e1, e2⟩ := hQ (sl, (Γ, s.2)) (sl, (Γ, (s.2.1, E)))
      ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, h⟩
    exact Prod.ext e1 e2⟩

/-- **Varying `H₂³` alone**: a table agreeing on the `H₂³` read set has the same read sets and
output. -/
lemma ConsP.h2 (hQ : ConsP Q f) (sl : SlP) (s : ShP R) (Γ Γ' : Tab2G pP)
    (h : ∀ k ∈ (Q (sl, (Γ, s.2))).2.1, Γ k = Γ' k) :
    Q (sl, (Γ', s.2)) = Q (sl, (Γ, s.2)) ∧ f (sl, (Γ', s.2)) = f (sl, (Γ, s.2)) :=
  hQ (sl, (Γ, s.2)) (sl, (Γ', s.2))
    ⟨fun _ _ => rfl, fun _ _ => rfl, h, fun _ _ => rfl, fun _ _ => rfl⟩

end Joint

/-! ## The joint budget and the Issuer with `H₂³` substituted -/

namespace AdversaryRA

variable (A : AdversaryRA R)

/-- **The interaction's joint budget**: the key-and-messages stage and the response stage at every
pair of requests are consistent readers of both slices and the shared tables (`SReadsP`), at most
`i₃` keys of each slice, `i₂` `H₂³` keys, `i₅` `H₅` keys and `i_E` cipher keys. -/
structure IBudgetH (i3 i2 i5 iE : ℕ) : Prop where
  k : SReadsP (fun t : TbP R => A.keyOf t.1 t.2) i3 i2 i5 iE
  r : ∀ t₀ t₁ : Bytes, SReadsP (fun t : TbP R => A.respOf t₀ t₁ t.1 t.2) i3 i2 i5 iE

/-- **The interaction's `H₂³` read set at the requests `t₀`, `t₁`**, with `H₂³ = Γ`: the key
stage's and the response stage's (`Qk`, `Qr` explicit read sets). -/
def mixQ (Qk : TbP R → RSP) (Qr : Bytes → Bytes → TbP R → RSP) (Γ : Tab2G pP) (t₀ t₁ : Bytes)
    (sl : SlP) (s₂ : Tab5F × (Blk → R)) : Finset (K2 pP) :=
  (Qk (sl, (Γ, s₂))).2.1 ∪ (Qr t₀ t₁ (sl, (Γ, s₂))).2.1

/-- **The Issuer with `H₂³` substituted**: its interaction reads `Γ` in place of `H₂³`, and its
guess sees `H₂³` patched with `Γ` at the interaction's read set at the requests it is shown. -/
def subst (Qk : TbP R → RSP) (Qr : Bytes → Bytes → TbP R → RSP) (Γ : Tab2G pP) : AdversaryRA R where
  pk sl s := A.pk sl (Γ, s.2)
  msg b sl s := A.msg b sl (Γ, s.2)
  respond t₀ t₁ i sl s := A.respond t₀ t₁ i sl (Γ, s.2)
  guess t₀ t₁ y sl s := A.guess t₀ t₁ y sl (patchT (mixQ Qk Qr Γ t₀ t₁ sl s.2) Γ s.1, s.2)

/-- The read sets of the Issuer with the roles exchanged. -/
def swapRS (r : RSP) : RSP := ((r.1.2, r.1.1), r.2)

lemma swap_subst (Qk : TbP R → RSP) (Qr : Bytes → Bytes → TbP R → RSP) (Γ : Tab2G pP) :
    A.swap.subst (fun t => swapRS (Qk ((t.1.2, t.1.1), t.2)))
        (fun t₀ t₁ t => swapRS (Qr t₁ t₀ ((t.1.2, t.1.1), t.2))) Γ =
      (A.subst Qk Qr Γ).swap := rfl

variable {A}

/-- **The joint budget of the Issuer with the roles exchanged.** -/
lemma consP_swapK {Qk : TbP R → RSP} (h : ConsP Qk fun t : TbP R => A.keyOf t.1 t.2) :
    ConsP (fun t => swapRS (Qk ((t.1.2, t.1.1), t.2))) fun t : TbP R => A.swap.keyOf t.1 t.2 :=
  fun t t' ⟨h1, h2, h3, h4, h5⟩ => by
    obtain ⟨e1, e2⟩ := h ((t.1.2, t.1.1), t.2) ((t'.1.2, t'.1.1), t'.2) ⟨h2, h1, h3, h4, h5⟩
    exact ⟨by simp only [e1], e2⟩

lemma consP_swapR {Qr : Bytes → Bytes → TbP R → RSP}
    (h : ∀ t₀ t₁, ConsP (Qr t₀ t₁) fun t : TbP R => A.respOf t₀ t₁ t.1 t.2) (t₀ t₁ : Bytes) :
    ConsP (fun t => swapRS (Qr t₁ t₀ ((t.1.2, t.1.1), t.2)))
      fun t : TbP R => A.swap.respOf t₀ t₁ t.1 t.2 :=
  fun t t' ⟨h1, h2, h3, h4, h5⟩ => by
    obtain ⟨e1, e2⟩ := h t₁ t₀ ((t.1.2, t.1.1), t.2) ((t'.1.2, t'.1.1), t'.2) ⟨h2, h1, h3, h4, h5⟩
    exact ⟨by simp only [e1], Prod.ext (congrArg Prod.snd e2) (congrArg Prod.fst e2)⟩

lemma cardP_swap {Q : TbP R → RSP} {a3 a2 a5 aE : ℕ} (h : CardP Q a3 a2 a5 aE) :
    CardP (fun t => swapRS (Q ((t.1.2, t.1.1), t.2))) a3 a2 a5 aE := fun t => by
  obtain ⟨c1, c2, c3, c4, c5⟩ := h ((t.1.2, t.1.1), t.2)
  exact ⟨c2, c1, c3, c4, c5⟩

/-- **The Issuer with `H₂³` substituted does not read `H₂³`**: its interaction's budget. -/
theorem IBudget.subst {Qk : TbP R → RSP} {Qr : Bytes → Bytes → TbP R → RSP} {i3 i2 i5 iE : ℕ}
    (hk : ConsP Qk fun t : TbP R => A.keyOf t.1 t.2) (hck : CardP Qk i3 i2 i5 iE)
    (hr : ∀ t₀ t₁, ConsP (Qr t₀ t₁) fun t : TbP R => A.respOf t₀ t₁ t.1 t.2)
    (hcr : ∀ t₀ t₁, CardP (Qr t₀ t₁) i3 i2 i5 iE) (Γ : Tab2G pP) :
    (A.subst Qk Qr Γ).IBudget i3 i5 iE where
  k0 g₁ := hk.at0 hck g₁ Γ
  k1 g₀ := hk.at1 hck g₀ Γ
  r0 t₀ t₁ g₁ := (hr t₀ t₁).at0 (hcr t₀ t₁) g₁ Γ
  r1 t₀ t₁ g₀ := (hr t₀ t₁).at1 (hcr t₀ t₁) g₀ Γ

/-- A reader of the shared tables through a change of `H₂³` reads the same `H₅` keys. -/
lemma Rd5.comp_h2 {X : Type*} {F : ShP R → X} {q : ℕ} (h : Rd5 F q) (φ : ShP R → Tab2G pP)
    (hφ : ∀ s G5, φ (s.1, G5, s.2.2) = φ s) : Rd5 (fun s => F (φ s, s.2)) q := by
  obtain ⟨Q, hQ, hf⟩ := h
  exact ⟨fun s => Q (φ s, s.2), fun s => hQ _, fun s G5 h' => by
    show F (φ (s.1, G5, s.2.2), G5, s.2.2) = F (φ s, s.2)
    rw [hφ s G5]; exact hf (φ s, s.2) G5 h'⟩

lemma RdE.comp_h2 {X : Type*} {F : ShP R → X} {q : ℕ} (h : RdE F q) (φ : ShP R → Tab2G pP)
    (hφ : ∀ s E, φ (s.1, s.2.1, E) = φ s) : RdE (fun s => F (φ s, s.2)) q := by
  obtain ⟨Q, hQ, hf⟩ := h
  exact ⟨fun s => Q (φ s, s.2), fun s => hQ _, fun s E h' => by
    show F (φ (s.1, s.2.1, E), s.2.1, E) = F (φ s, s.2)
    rw [hφ s E]; exact hf (φ s, s.2) E h'⟩

/-- **The guess of the Issuer with `H₂³` substituted** reads the guess's keys and the
interaction's (key stage and response stage) read sets' keys. -/
theorem GBudget.subst {Qk : TbP R → RSP} {Qr : Bytes → Bytes → TbP R → RSP}
    {q3 q5 qE i3 i2 i5 iE : ℕ} (hA : A.GBudget q3 q5 qE)
    (hk : ConsP Qk fun t : TbP R => A.keyOf t.1 t.2) (hck : CardP Qk i3 i2 i5 iE)
    (hr : ∀ t₀ t₁, ConsP (Qr t₀ t₁) fun t : TbP R => A.respOf t₀ t₁ t.1 t.2)
    (hcr : ∀ t₀ t₁, CardP (Qr t₀ t₁) i3 i2 i5 iE) (Γ : Tab2G pP) :
    (A.subst Qk Qr Γ).GBudget (i3 + i3 + q3) (i5 + i5 + q5) (iE + iE + qE) where
  h30 t₀ t₁ y g₁ s := by
    have hm : Rd3 (fun g => mixQ Qk Qr Γ t₀ t₁ (g, g₁) s.2) (i3 + i3) := by
      have := ((hk.rd30 hck g₁ (Γ, s.2)).bind (f := fun a g => (a, Qr t₀ t₁ ((g, g₁), (Γ, s.2))))
        fun a => ((hr t₀ t₁).rd30 (hcr t₀ t₁) g₁ (Γ, s.2)).map fun b => (a, b.1))
      exact this.map fun ab => ab.1.1.2.1 ∪ ab.2.2.1
    exact hm.bind (f := fun M g => A.guess t₀ t₁ y (g, g₁) (patchT M Γ s.1, s.2)) fun M =>
      hA.h30 t₀ t₁ y g₁ (patchT M Γ s.1, s.2)
  h31 t₀ t₁ y g₀ s := by
    have hm : Rd3 (fun g => mixQ Qk Qr Γ t₀ t₁ (g₀, g) s.2) (i3 + i3) := by
      have := ((hk.rd31 hck g₀ (Γ, s.2)).bind (f := fun a g => (a, Qr t₀ t₁ ((g₀, g), (Γ, s.2))))
        fun a => ((hr t₀ t₁).rd31 (hcr t₀ t₁) g₀ (Γ, s.2)).map fun b => (a, b.1))
      exact this.map fun ab => ab.1.1.2.1 ∪ ab.2.2.1
    exact hm.bind (f := fun M g => A.guess t₀ t₁ y (g₀, g) (patchT M Γ s.1, s.2)) fun M =>
      hA.h31 t₀ t₁ y g₀ (patchT M Γ s.1, s.2)
  h5 t₀ t₁ y sl := by
    have hm : Rd5 (fun s : ShP R => mixQ Qk Qr Γ t₀ t₁ sl s.2) (i5 + i5) := by
      have := ((hk.rd5 hck sl Γ).bind (f := fun a s => (a, Qr t₀ t₁ (sl, (Γ, s.2))))
        fun a => ((hr t₀ t₁).rd5 (hcr t₀ t₁) sl Γ).map fun b => (a, b.1))
      exact this.map fun ab => ab.1.1.2.1 ∪ ab.2.2.1
    exact hm.bind (f := fun M s => A.guess t₀ t₁ y sl (patchT M Γ s.1, s.2)) fun M =>
      Rd5.comp_h2 (hA.h5 t₀ t₁ y sl) (fun s => patchT M Γ s.1) fun _ _ => rfl
  hE t₀ t₁ y sl := by
    have hm : RdE (fun s : ShP R => mixQ Qk Qr Γ t₀ t₁ sl s.2) (iE + iE) := by
      have := ((hk.rdE hck sl Γ).bind (f := fun a s => (a, Qr t₀ t₁ (sl, (Γ, s.2))))
        fun a => ((hr t₀ t₁).rdE (hcr t₀ t₁) sl Γ).map fun b => (a, b.1))
      exact this.map fun ab => ab.1.1.2.1 ∪ ab.2.2.1
    exact hm.bind (f := fun M s => A.guess t₀ t₁ y sl (patchT M Γ s.1, s.2)) fun M =>
      RdE.comp_h2 (hA.hE t₀ t₁ y sl) (fun s => patchT M Γ s.1) fun _ _ => rfl

end AdversaryRA

/-! ## `G0` reads the Issuer only at its key, messages and responses to the actual requests -/

section G0Congr

variable (Hb : Hashes) {A₁ A₂ : AdversaryRO R}

/-- **`G0` reads the Issuer at its key and messages, its guess, and its responses to the two
requests.** -/
lemma G0_congr (h : A₁.pk = A₂.pk) (hg : A₁.guess = A₂.guess) (h0 : A₁.msg false = A₂.msg false)
    (h1 : A₁.msg true = A₂.msg true) (z : (XR × XR) × ShP R)
    (hr : ∀ i, A₁.respond (tR Hb A₁ (A₁.msg false) z.1.1 z.2) (tR Hb A₁ (A₁.msg true) z.1.2 z.2) i =
      A₂.respond (tR Hb A₁ (A₁.msg false) z.1.1 z.2) (tR Hb A₁ (A₁.msg true) z.1.2 z.2) i) :
    G0 Hb A₁ z ↔ G0 Hb A₂ z := by
  obtain ⟨⟨x₀, x₁⟩, s⟩ := z
  have ht := tOf_congr (R := R) h
  have hk0 : kOf A₁ (A₁.msg false) x₀.1.2.1 x₀.1.2.2 false (tR Hb A₁ (A₁.msg true) x₁ s)
      (s1R Hb x₀ s) =
      kOf A₂ (A₁.msg false) x₀.1.2.1 x₀.1.2.2 false (tR Hb A₁ (A₁.msg true) x₁ s) (s1R Hb x₀ s) :=
    kOf_congr h _ _ _ false _ _ fun j => hr j
  have hO := oR_congr Hb (A₁ := A₁) (A₂ := A₂) (A₁.msg false) false x₀ (tR Hb A₁ (A₁.msg true) x₁)
    s hk0
  have hR : tR Hb A₁ (A₁.msg true) x₁ = tR Hb A₂ (A₂.msg true) x₁ := by
    funext s'; simp only [tR, ht, h1]
  have e1 : G0 Hb A₁ ((x₀, x₁), s) ↔ D0 Hb A₁ x₀.1.2.1 x₀.1.2.2 x₁
      (oR Hb A₁ (A₁.msg false) false x₀ (tR Hb A₁ (A₁.msg true) x₁) s) x₀.2 s := Iff.rfl
  have e2 : G0 Hb A₂ ((x₀, x₁), s) ↔ D0 Hb A₂ x₀.1.2.1 x₀.1.2.2 x₁
      (oR Hb A₂ (A₂.msg false) false x₀ (tR Hb A₂ (A₂.msg true) x₁) s) x₀.2 s := Iff.rfl
  rw [e1, e2, ← hR, ← h0, ← hO]
  refine D0_congr Hb h hg h0 h1 x₀.1.2.1 x₀.1.2.2 x₁ _ x₀.2 s fun i => ?_
  rw [oR_s1]
  exact hr i

/-- **`G0` at the Issuer at the tables `u`** is `G0` at the Issuer with its key and its responses
to the two requests fixed. -/
lemma G0_fix (A : AdversaryRA R) (sl : SlP) (u : ShP R) (z : (XR × XR) × ShP R) :
    G0 Hb (A.at sl u) z ↔
      G0 Hb (A.fix (A.keyOf sl u) (A.respOf
          (tK (A.keyOf sl u) (A.msg false sl u) z.1.1.1.2.1 z.1.1.1.2.2 (s1R Hb z.1.1 z.2))
          (tK (A.keyOf sl u) (A.msg true sl u) z.1.2.1.2.1 z.1.2.1.2.2 (s1R Hb z.1.2 z.2)) sl u)) z := by
  have ht : tOf (A.at sl u) = tK (A.keyOf sl u) := tOf_eq_tK rfl
  refine G0_congr Hb (A₁ := A.at sl u) (A₂ := A.fix (A.keyOf sl u) (A.respOf
      (tK (A.keyOf sl u) (A.msg false sl u) z.1.1.1.2.1 z.1.1.1.2.2 (s1R Hb z.1.1 z.2))
      (tK (A.keyOf sl u) (A.msg true sl u) z.1.2.1.2.1 z.1.2.1.2.2 (s1R Hb z.1.2 z.2)) sl u))
    rfl rfl rfl rfl z fun i => ?_
  cases i <;> (rw [tR, tR, ht]; rfl)

end G0Congr

/-! ## Lazy sampling with the reader depending on the other coins -/

/-- **`Privacy.pr_resample` with the reader and its read sets depending on other coins `C`.** -/
theorem pr_resampleC {T Rr C X : Type*} [Fintype T] [Nonempty T] [Fintype C]
    (mix : Rr → T → T → T) (Ag : Rr → T → T → Prop) (hag : ∀ r a b, Ag r a (mix r a b))
    (hinv : ∀ r a b, mix r (mix r a b) (mix r b a) = a)
    (S : C → T → X) (Q : C → T → Rr)
    (hS : ∀ c t t', Ag (Q c t) t t' → Q c t' = Q c t ∧ S c t' = S c t) (F : C → X → T → Prop) :
    pr (C × T) (fun z => F z.1 (S z.1 z.2) z.2) =
      pr ((C × T) × T) (fun z => F z.1.1 (S z.1.1 z.1.2) (mix (Q z.1.1 z.1.2) z.1.2 z.2)) := by
  let φ : C → T × T → T × T := fun c ab => (mix (Q c ab.1) ab.1 ab.2, mix (Q c ab.1) ab.2 ab.1)
  have hφ : ∀ c ab, φ c (φ c ab) = ab := by
    rintro c ⟨a, b⟩
    have hQ : Q c (mix (Q c a) a b) = Q c a := (hS c a _ (hag _ a b)).1
    simp only [φ, hQ, hinv]
  let e : C × (T × T) ≃ C × (T × T) :=
    ⟨fun w => (w.1, φ w.1 w.2), fun w => (w.1, φ w.1 w.2), fun w => Prod.ext rfl (hφ w.1 w.2),
      fun w => Prod.ext rfl (hφ w.1 w.2)⟩
  let E : (C × T) × T ≃ C × (T × T) := Equiv.prodAssoc C T T
  have h1 : pr (C × T) (fun z => F z.1 (S z.1 z.2) z.2) =
      pr (C × (T × T)) (fun w => F w.1 (S w.1 w.2.1) w.2.1) := by
    rw [← pr_prod_fst (β := T) (fun z : C × T => F z.1 (S z.1 z.2) z.2), ← pr_equiv E.symm]
    rfl
  have h2 : pr (C × (T × T)) (fun w => F w.1 (S w.1 w.2.1) w.2.1) =
      pr (C × (T × T)) (fun w => F (e w).1 (S (e w).1 (e w).2.1) (e w).2.1) :=
    (pr_equiv e (fun w => F w.1 (S w.1 w.2.1) w.2.1)).symm
  have h3 : pr (C × (T × T)) (fun w => F (e w).1 (S (e w).1 (e w).2.1) (e w).2.1) =
      pr (C × (T × T)) (fun w => F w.1 (S w.1 w.2.1) (mix (Q w.1 w.2.1) w.2.1 w.2.2)) := by
    refine pr_congr fun w => ?_
    show F w.1 (S w.1 (mix (Q w.1 w.2.1) w.2.1 w.2.2)) (mix (Q w.1 w.2.1) w.2.1 w.2.2) ↔ _
    rw [(hS w.1 w.2.1 _ (hag _ w.2.1 w.2.2)).2]
  rw [h1, h2, h3, ← pr_equiv E]
  rfl

/-! ## The Issuer at the tables with `H₂³` substituted -/

section SubstAt

variable (A : AdversaryRA R) (Qk : TbP R → RSP) (Qr : Bytes → Bytes → TbP R → RSP) (Γ : Tab2G pP)

lemma tOf_subst (sl : SlP) (s : ShP R) :
    tOf ((A.subst Qk Qr Γ).at sl s) = tOf (A.at sl (Γ, s.2)) := rfl

lemma bothOK_subst (sl : SlP) (s : ShP R) :
    bothOK ((A.subst Qk Qr Γ).at sl s) = bothOK (A.at sl (Γ, s.2)) := rfl

lemma kOf_subst (sl : SlP) (s : ShP R) :
    kOf ((A.subst Qk Qr Γ).at sl s) = kOf (A.at sl (Γ, s.2)) := rfl

lemma oR_subst (Hb : Hashes) (sl : SlP) (s : ShP R) :
    oR Hb ((A.subst Qk Qr Γ).at sl s) = oR Hb (A.at sl (Γ, s.2)) := rfl

lemma tR_subst (Hb : Hashes) (sl : SlP) (s : ShP R) :
    tR Hb ((A.subst Qk Qr Γ).at sl s) = tR Hb (A.at sl (Γ, s.2)) := rfl

lemma msg_subst (sl : SlP) (s : ShP R) (b : Bool) :
    ((A.subst Qk Qr Γ).at sl s).msg b = (A.at sl (Γ, s.2)).msg b := rfl

end SubstAt

/-! ## Lazy sampling of the interaction's `H₂³` reads -/

section Resample

variable (Hb : Hashes) (A : AdversaryRA R) (Qk : TbP R → RSP) (Qr : Bytes → Bytes → TbP R → RSP)

/-- **The coins of the game other than `H₂³`**: both sessions' tapes, `H₅` and the cipher. -/
abbrev CH (R : Type) := (XR × XR) × (Tab5F × (Blk → R))

/-- The slices of the coins. -/
def slH (c : CH R) : SlP := (c.1.1.2, c.1.2.2)

/-- The game's tape from the coins and `H₂³`. -/
def zH (c : CH R) (G2 : Tab2G pP) : (XR × XR) × ShP R := (c.1, (G2, c.2))

/-- **The two requests**, with the interaction at `H₂³ = Γ`. -/
noncomputable def tqH (c : CH R) (Γ : Tab2G pP) : Bytes × Bytes :=
  (tK (A.keyOf (slH c) (Γ, c.2)) (A.msg false (slH c) (Γ, c.2)) c.1.1.1.2.1 c.1.1.1.2.2
      (s1R Hb c.1.1 (Γ, c.2)),
    tK (A.keyOf (slH c) (Γ, c.2)) (A.msg true (slH c) (Γ, c.2)) c.1.2.1.2.1 c.1.2.1.2.2
      (s1R Hb c.1.2 (Γ, c.2)))

/-- **The interaction's values** at `H₂³ = Γ`: the key and messages, the responses to the two
requests. -/
noncomputable def intH (c : CH R) (Γ : Tab2G pP) : (UOVKey × Bytes × Bytes) × (Bytes × Bytes) :=
  (A.keyOf (slH c) (Γ, c.2), A.respOf (tqH Hb A c Γ).1 (tqH Hb A c Γ).2 (slH c) (Γ, c.2))

/-- **The interaction's `H₂³` read set** at `H₂³ = Γ`. -/
noncomputable def readH (c : CH R) (Γ : Tab2G pP) : Finset (K2 pP) :=
  AdversaryRA.mixQ Qk Qr Γ (tqH Hb A c Γ).1 (tqH Hb A c Γ).2 (slH c) c.2

variable {A Qk Qr}

/-- **The interaction is a consistent reader of `H₂³`** (the rest fixed). -/
lemma readH_cons (hk : ConsP Qk fun t : TbP R => A.keyOf t.1 t.2)
    (hr : ∀ t₀ t₁, ConsP (Qr t₀ t₁) fun t : TbP R => A.respOf t₀ t₁ t.1 t.2) (c : CH R)
    (Γ Γ' : Tab2G pP) (h : ∀ κ ∈ readH Hb A Qk Qr c Γ, Γ κ = Γ' κ) :
    readH Hb A Qk Qr c Γ' = readH Hb A Qk Qr c Γ ∧ intH Hb A c Γ' = intH Hb A c Γ := by
  obtain ⟨ek1, ek2⟩ := hk.h2 (slH c) (Γ, c.2) Γ Γ' fun κ hκ => h κ (mem_union_left _ hκ)
  have ek2' : A.keyOf (slH c) (Γ', c.2) = A.keyOf (slH c) (Γ, c.2) := ek2
  have hm0 : A.msg false (slH c) (Γ', c.2) = A.msg false (slH c) (Γ, c.2) :=
    congrArg (fun P : UOVKey × Bytes × Bytes => P.2.1) ek2'
  have hm1 : A.msg true (slH c) (Γ', c.2) = A.msg true (slH c) (Γ, c.2) :=
    congrArg (fun P : UOVKey × Bytes × Bytes => P.2.2) ek2'
  have hs0 : s1R Hb c.1.1 (Γ', c.2) = s1R Hb c.1.1 (Γ, c.2) := s1R_h23 Hb c.1.1 (Γ, c.2) Γ'
  have hs1 : s1R Hb c.1.2 (Γ', c.2) = s1R Hb c.1.2 (Γ, c.2) := s1R_h23 Hb c.1.2 (Γ, c.2) Γ'
  have htq : tqH Hb A c Γ' = tqH Hb A c Γ := by
    simp only [tqH, ek2', hm0, hm1, hs0, hs1]
  obtain ⟨er1, er2⟩ := (hr (tqH Hb A c Γ).1 (tqH Hb A c Γ).2).h2 (slH c) (Γ, c.2) Γ Γ'
    fun κ hκ => h κ (mem_union_right _ hκ)
  have ek1' : Qk (slH c, (Γ', c.2)) = Qk (slH c, (Γ, c.2)) := ek1
  have er1' : Qr (tqH Hb A c Γ).1 (tqH Hb A c Γ).2 (slH c, (Γ', c.2)) =
      Qr (tqH Hb A c Γ).1 (tqH Hb A c Γ).2 (slH c, (Γ, c.2)) := er1
  have er2' : A.respOf (tqH Hb A c Γ).1 (tqH Hb A c Γ).2 (slH c) (Γ', c.2) =
      A.respOf (tqH Hb A c Γ).1 (tqH Hb A c Γ).2 (slH c) (Γ, c.2) := er2
  refine ⟨?_, ?_⟩
  · simp only [readH, AdversaryRA.mixQ, htq, ek1', er1']
  · simp only [intH, htq, ek2', er2']

end Resample

/-! ## The game with the interaction resampled -/

section Resampled

variable (Hb : Hashes) (A : AdversaryRA R) (Qk : TbP R → RSP) (Qr : Bytes → Bytes → TbP R → RSP)

/-- Regroup the game's tape as the coins and `H₂³`. -/
def eqCH : CH R × Tab2G pP ≃ (XR × XR) × ShP R where
  toFun w := zH w.1 w.2
  invFun z := ((z.1, z.2.2), z.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The game with the interaction's values fixed** (`I`: key, messages, the two responses). -/
def GF (c : CH R) (I : (UOVKey × Bytes × Bytes) × (Bytes × Bytes)) (G2 : Tab2G pP) : Prop :=
  G0 Hb (A.fix I.1 I.2) (zH c G2)

variable {A Qk Qr}

/-- **Lazy sampling of the interaction's `H₂³` reads**: the game is the game with the interaction
at an independent `Γ` and `H₂³` patched with `Γ` at the interaction's read set. -/
theorem pr_G0RA_resample (hk : ConsP Qk fun t : TbP R => A.keyOf t.1 t.2)
    (hr : ∀ t₀ t₁, ConsP (Qr t₀ t₁) fun t : TbP R => A.respOf t₀ t₁ t.1 t.2) :
    pr ((XR × XR) × ShP R) (G0RA Hb A) =
      pr ((CH R × Tab2G pP) × Tab2G pP) (fun w => GF Hb A w.1.1 (intH Hb A w.1.1 w.1.2)
        (patchT (readH Hb A Qk Qr w.1.1 w.1.2) w.1.2 w.2)) := by
  rw [← pr_equiv eqCH (G0RA Hb A)]
  have e : ∀ w : CH R × Tab2G pP, G0RA Hb A (eqCH w) ↔ GF Hb A w.1 (intH Hb A w.1 w.2) w.2 :=
    fun w => G0_fix Hb A (slH w.1) (w.2, w.1.2) (zH w.1 w.2)
  rw [pr_congr e]
  exact pr_resampleC (fun P a b => patchT P a b) (fun P a b => ∀ κ ∈ P, a κ = b κ)
    (fun P a b κ hκ => (patchT_of_mem a b hκ).symm) (fun P a b => patchT_patchT_swap P a b)
    (intH Hb A) (readH Hb A Qk Qr) (fun c t t' h => readH_cons Hb hk hr c t t' h) (GF Hb A)

variable (A Qk Qr)

/-- **The collision**: a session's real run, with the interaction at `Γ`, reads `H₂³` differently
on the table patched at the interaction's read set. -/
def badH (c : CH R) (Γ G2 : Tab2G pP) : Prop :=
  oR Hb (A.at (slH c) (Γ, c.2)) ((A.at (slH c) (Γ, c.2)).msg false) false c.1.1
      (tR Hb (A.at (slH c) (Γ, c.2)) ((A.at (slH c) (Γ, c.2)).msg true) c.1.2)
      (patchT (readH Hb A Qk Qr c Γ) Γ G2, c.2) ≠
    oR Hb (A.at (slH c) (Γ, c.2)) ((A.at (slH c) (Γ, c.2)).msg false) false c.1.1
      (tR Hb (A.at (slH c) (Γ, c.2)) ((A.at (slH c) (Γ, c.2)).msg true) c.1.2) (G2, c.2) ∨
  oR Hb (A.at (slH c) (Γ, c.2)) ((A.at (slH c) (Γ, c.2)).msg true) true c.1.2
      (tR Hb (A.at (slH c) (Γ, c.2)) ((A.at (slH c) (Γ, c.2)).msg false) c.1.1)
      (patchT (readH Hb A Qk Qr c Γ) Γ G2, c.2) ≠
    oR Hb (A.at (slH c) (Γ, c.2)) ((A.at (slH c) (Γ, c.2)).msg true) true c.1.2
      (tR Hb (A.at (slH c) (Γ, c.2)) ((A.at (slH c) (Γ, c.2)).msg false) c.1.1) (G2, c.2)

variable {A Qk Qr}

/-- The game with the interaction's values is the game at the Issuer at `(Γ, H₅, E)`. -/
lemma GF_iff_at (c : CH R) (Γ G2 : Tab2G pP) :
    GF Hb A c (intH Hb A c Γ) G2 ↔ G0 Hb (A.at (slH c) (Γ, c.2)) (zH c G2) := by
  have hs0 : s1R Hb c.1.1 (G2, c.2) = s1R Hb c.1.1 (Γ, c.2) := s1R_h23 Hb c.1.1 (Γ, c.2) G2
  have hs1 : s1R Hb c.1.2 (G2, c.2) = s1R Hb c.1.2 (Γ, c.2) := s1R_h23 Hb c.1.2 (Γ, c.2) G2
  have ht : tOf (A.fix (intH Hb A c Γ).1 (intH Hb A c Γ).2) = tK (A.keyOf (slH c) (Γ, c.2)) :=
    tOf_eq_tK rfl
  refine G0_congr Hb (A₁ := A.fix (intH Hb A c Γ).1 (intH Hb A c Γ).2)
    (A₂ := A.at (slH c) (Γ, c.2)) rfl rfl rfl rfl (zH c G2) fun i => ?_
  have e0 : tR Hb (A.fix (intH Hb A c Γ).1 (intH Hb A c Γ).2)
      ((A.fix (intH Hb A c Γ).1 (intH Hb A c Γ).2).msg false) (zH c G2).1.1 (zH c G2).2 =
      (tqH Hb A c Γ).1 := by
    show tOf _ _ _ _ (s1R Hb c.1.1 (G2, c.2)) = _
    rw [ht, hs0]; rfl
  have e1 : tR Hb (A.fix (intH Hb A c Γ).1 (intH Hb A c Γ).2)
      ((A.fix (intH Hb A c Γ).1 (intH Hb A c Γ).2).msg true) (zH c G2).1.2 (zH c G2).2 =
      (tqH Hb A c Γ).2 := by
    show tOf _ _ _ _ (s1R Hb c.1.2 (G2, c.2)) = _
    rw [ht, hs1]; rfl
  rw [e0, e1]
  cases i <;> rfl

/-- **The view at the Issuer with `H₂³` substituted** is the view at the Issuer at `Γ` with the
guess shown `H₂³` patched at the interaction's read set at the requests. -/
lemma view2_subst (b : Bool) (m₀ m₁ : Bytes × Coins refresherBytes × Coins uovM) (o₀ o₁ : Out2)
    (sl : SlP) (Γ G2 : Tab2G pP) (s₂ : Tab5F × (Blk → R)) :
    view2 ((A.subst Qk Qr Γ).at sl (G2, s₂)) b m₀ m₁ o₀ o₁ sl (G2, s₂) ↔
      view2 (A.at sl (Γ, s₂)) b m₀ m₁ o₀ o₁ sl
        (patchT (AdversaryRA.mixQ Qk Qr Γ (tOf (A.at sl (Γ, s₂)) m₀.1 m₀.2.1 m₀.2.2 (o₀.1, o₀.2.1))
          (tOf (A.at sl (Γ, s₂)) m₁.1 m₁.2.1 m₁.2.2 (o₁.1, o₁.2.1)) sl s₂) Γ G2, s₂) := Iff.rfl

/-- **Unless a session's run reads a patched point, the patched game is the game of the Issuer
with `H₂³` substituted** on the unpatched table. -/
lemma G0_at_iff_subst (c : CH R) (Γ G2 : Tab2G pP) (hb : ¬ badH Hb A Qk Qr c Γ G2) :
    G0 Hb (A.at (slH c) (Γ, c.2)) (zH c (patchT (readH Hb A Qk Qr c Γ) Γ G2)) ↔
      G0RA Hb (A.subst Qk Qr Γ) (zH c G2) := by
  obtain ⟨⟨x₀, x₁⟩, s₂⟩ := c
  have hb0 := not_not.1 (not_or.1 hb).1
  have hb1 := not_not.1 (not_or.1 hb).2
  simp only [slH] at hb0 hb1 ⊢
  -- Session 1's continuation reads session 0's request off its step-1 output.
  have hc1 : ∀ v : ShP R,
      oR Hb (A.at (x₀.2, x₁.2) (Γ, s₂)) ((A.at (x₀.2, x₁.2) (Γ, s₂)).msg true) true x₁
        (fun _ => tOf (A.at (x₀.2, x₁.2) (Γ, s₂)) ((A.at (x₀.2, x₁.2) (Γ, s₂)).msg false)
          x₀.1.2.1 x₀.1.2.2
          ((oR Hb (A.at (x₀.2, x₁.2) (Γ, s₂)) ((A.at (x₀.2, x₁.2) (Γ, s₂)).msg false) false x₀
            (tR Hb (A.at (x₀.2, x₁.2) (Γ, s₂)) ((A.at (x₀.2, x₁.2) (Γ, s₂)).msg true) x₁) v).1,
          (oR Hb (A.at (x₀.2, x₁.2) (Γ, s₂)) ((A.at (x₀.2, x₁.2) (Γ, s₂)).msg false) false x₀
            (tR Hb (A.at (x₀.2, x₁.2) (Γ, s₂)) ((A.at (x₀.2, x₁.2) (Γ, s₂)).msg true) x₁) v).2.1))
        v =
      oR Hb (A.at (x₀.2, x₁.2) (Γ, s₂)) ((A.at (x₀.2, x₁.2) (Γ, s₂)).msg true) true x₁
        (tR Hb (A.at (x₀.2, x₁.2) (Γ, s₂)) ((A.at (x₀.2, x₁.2) (Γ, s₂)).msg false) x₀) v :=
    fun v => oR_cont Hb _ _ true x₁ v (by rw [oR_s1]; rfl)
  have hs0 : s1R Hb x₀ (G2, s₂) = s1R Hb x₀ (Γ, s₂) := s1R_h23 Hb x₀ (Γ, s₂) G2
  have hs1 : s1R Hb x₁ (G2, s₂) = s1R Hb x₁ (Γ, s₂) := s1R_h23 Hb x₁ (Γ, s₂) G2
  have ht : tOf (A.at (x₀.2, x₁.2) (Γ, s₂)) = tK (A.keyOf (x₀.2, x₁.2) (Γ, s₂)) := tOf_eq_tK rfl
  unfold G0RA G0
  simp only [zH, tR_subst, oR_subst, msg_subst, tOf_subst]
  rw [hc1, hc1, hb0, hb1, view2_subst, oR_s1, oR_s1, hs0, hs1, ht]
  rfl

end Resampled

/-! ## Session `1`'s continuation with session `0` real -/

section K1R

variable (Hb : Hashes) {A : AdversaryRA R}

/-- **Session `1`'s continuation, session `0` real.** -/
lemma kOf_fixR1 (sl : SlP) (s : ShP R) (ref₁ : Coins refresherBytes) (r₁ : Coins uovM) (x₀ : XR)
    (o1 : ByteArray × ByteArray) :
    kOf (A.at sl s) ((A.at sl s).msg true) ref₁ r₁ true
        (tR Hb (A.at sl s) ((A.at sl s).msg false) x₀ s) o1 =
      kOf (A.fix (A.keyOf sl s) (A.respOf
          (tK (A.keyOf sl s) (A.msg false sl s) x₀.1.2.1 x₀.1.2.2 (s1R Hb x₀ s))
          (tK (A.keyOf sl s) (A.msg true sl s) ref₁ r₁ o1) sl s))
        (A.msg true sl s) ref₁ r₁ true
        (tK (A.keyOf sl s) (A.msg false sl s) x₀.1.2.1 x₀.1.2.2 (s1R Hb x₀ s)) o1 := by
  have ht : tOf (A.at sl s) = tK (A.keyOf sl s) := tOf_eq_tK rfl
  have hR : tR Hb (A.at sl s) ((A.at sl s).msg false) x₀ s =
      tK (A.keyOf sl s) (A.msg false sl s) x₀.1.2.1 x₀.1.2.2 (s1R Hb x₀ s) := by
    rw [tR, ht]; rfl
  rw [hR]
  refine kOf_congr rfl _ _ _ true _ _ fun j => ?_
  cases j <;> (rw [ht]; try rfl)

variable (A) in
/-- **Session `1`'s continuation with session `0` real**: the Issuer at the tables (with session
`1`'s slice `g`) answers session `0`'s request and the request of session `1`'s step-1 output. -/
noncomputable def K1R (ref₁ : Coins refresherBytes) (r₁ : Coins uovM) (x₀ : XR) (g : Tab3)
    (s : ShP R) : Cont2 :=
  kOf (A.at (x₀.2, g) s) ((A.at (x₀.2, g) s).msg true) ref₁ r₁ true
    (tR Hb (A.at (x₀.2, g) s) ((A.at (x₀.2, g) s).msg false) x₀ s)

lemma K1R_h23 {i3 i5 iE : ℕ} (hI : A.IBudget i3 i5 iE) (ref₁ : Coins refresherBytes)
    (r₁ : Coins uovM) (x₀ : XR) (g : Tab3) (s : ShP R) (G2 : Tab2G pP) :
    K1R Hb A ref₁ r₁ x₀ g (G2, s.2) = K1R Hb A ref₁ r₁ x₀ g s := by
  unfold K1R
  rw [hI.at_h23, tR, tR, s1R_h23]

/-- **The hypotheses of `zk2_adaptive` for session `1`'s continuation with session `0` real**:
session `1`'s slice at `2·i₃` keys, `H₅` at `2·i₅ + 624` and the cipher at `2·i_E + 4607` keys
(the key stage, session `0`'s step 1 for its request, the response stage). -/
theorem hyp2RA_R1 (hHb : HashesWF Hb) {i3 i5 iE : ℕ} (hI : A.IBudget i3 i5 iE)
    (ref₁ : Coins refresherBytes) (r₁ : Coins uovM) (x₀ : XR) :
    Hyp2RA (stOf ref₁) (toBA (List.ofFn r₁)) uovM (K1R Hb A ref₁ r₁ x₀) (i3 + i3) (i5 + 624 + i5)
      (iE + 4607 + iE) where
  hyp g s := hyp2_kOf _ _ _ _ _ _
  size := by rw [size_toBA, List.length_ofFn]
  h2 g s G2 := K1R_h23 Hb hI ref₁ r₁ x₀ g s G2
  h3 o1 s := Rd3.bind' (m := fun g => A.keyOf (x₀.2, g) s)
    (f := fun P g => kOf (A.fix P (A.respOf (tK P P.2.1 x₀.1.2.1 x₀.1.2.2 (s1R Hb x₀ s))
        (tK P P.2.2 ref₁ r₁ o1) (x₀.2, g) s))
      P.2.2 ref₁ r₁ true (tK P P.2.1 x₀.1.2.1 x₀.1.2.2 (s1R Hb x₀ s)) o1)
    (fun g => kOf_fixR1 Hb (x₀.2, g) s ref₁ r₁ x₀ o1) ((hI.k1 x₀.2).rd3 s)
    (fun P => ((hI.r1 (tK P P.2.1 x₀.1.2.1 x₀.1.2.2 (s1R Hb x₀ s)) (tK P P.2.2 ref₁ r₁ o1)
      x₀.2).rd3 s).map fun Rr => kOf (A.fix P Rr) P.2.2 ref₁ r₁ true
        (tK P P.2.1 x₀.1.2.1 x₀.1.2.2 (s1R Hb x₀ s)) o1)
  h5 o1 g := Rd5.bind' (m := fun s => (A.keyOf (x₀.2, g) s, s1R Hb x₀ s))
    (f := fun Py s => kOf (A.fix Py.1 (A.respOf (tK Py.1 Py.1.2.1 x₀.1.2.1 x₀.1.2.2 Py.2)
        (tK Py.1 Py.1.2.2 ref₁ r₁ o1) (x₀.2, g) s))
      Py.1.2.2 ref₁ r₁ true (tK Py.1 Py.1.2.1 x₀.1.2.1 x₀.1.2.2 Py.2) o1)
    (fun s => kOf_fixR1 Hb (x₀.2, g) s ref₁ r₁ x₀ o1)
    (((hI.k1 x₀.2).rd5 g).bind fun P => (s1R_rd5 Hb x₀).map fun y => (P, y))
    (fun Py => ((hI.r1 (tK Py.1 Py.1.2.1 x₀.1.2.1 x₀.1.2.2 Py.2) (tK Py.1 Py.1.2.2 ref₁ r₁ o1)
      x₀.2).rd5 g).map fun Rr => kOf (A.fix Py.1 Rr) Py.1.2.2 ref₁ r₁ true
        (tK Py.1 Py.1.2.1 x₀.1.2.1 x₀.1.2.2 Py.2) o1)
  hE o1 g := RdE.bind' (m := fun s => (A.keyOf (x₀.2, g) s, s1R Hb x₀ s))
    (f := fun Py s => kOf (A.fix Py.1 (A.respOf (tK Py.1 Py.1.2.1 x₀.1.2.1 x₀.1.2.2 Py.2)
        (tK Py.1 Py.1.2.2 ref₁ r₁ o1) (x₀.2, g) s))
      Py.1.2.2 ref₁ r₁ true (tK Py.1 Py.1.2.1 x₀.1.2.1 x₀.1.2.2 Py.2) o1)
    (fun s => kOf_fixR1 Hb (x₀.2, g) s ref₁ r₁ x₀ o1)
    (((hI.k1 x₀.2).rdE g).bind fun P => (s1R_rdE Hb hHb x₀).map fun y => (P, y))
    (fun Py => ((hI.r1 (tK Py.1 Py.1.2.1 x₀.1.2.1 x₀.1.2.2 Py.2) (tK Py.1 Py.1.2.2 ref₁ r₁ o1)
      x₀.2).rdE g).map fun Rr => kOf (A.fix Py.1 Rr) Py.1.2.2 ref₁ r₁ true
        (tK Py.1 Py.1.2.1 x₀.1.2.1 x₀.1.2.2 Py.2) o1)

end K1R

/-! ## The interaction's read set, read off a session's step-1 output -/

section QF

variable (Hb : Hashes) (A : AdversaryRA R) (Qk : TbP R → RSP) (Qr : Bytes → Bytes → TbP R → RSP)
  (Γ : Tab2G pP)

/-- **The read set for session `0`** (session `1` real with tape `x₁`), at session `0`'s step-1
output `o1` and slice `g`. -/
noncomputable def qf0 (ref₀ : Coins refresherBytes) (r₀ : Coins uovM) (x₁ : XR)
    (o1 : ByteArray × ByteArray) (g : Tab3) (s : ShP R) : Finset (K2 pP) :=
  AdversaryRA.mixQ Qk Qr Γ
    (tK (A.keyOf (g, x₁.2) (Γ, s.2)) (A.keyOf (g, x₁.2) (Γ, s.2)).2.1 ref₀ r₀ o1)
    (tK (A.keyOf (g, x₁.2) (Γ, s.2)) (A.keyOf (g, x₁.2) (Γ, s.2)).2.2 x₁.1.2.1 x₁.1.2.2
      (s1R Hb x₁ s)) (g, x₁.2) s.2

/-- **The read set for session `1`** (session `0` real with tape `x₀`). -/
noncomputable def qf1 (ref₁ : Coins refresherBytes) (r₁ : Coins uovM) (x₀ : XR)
    (o1 : ByteArray × ByteArray) (g : Tab3) (s : ShP R) : Finset (K2 pP) :=
  AdversaryRA.mixQ Qk Qr Γ
    (tK (A.keyOf (x₀.2, g) (Γ, s.2)) (A.keyOf (x₀.2, g) (Γ, s.2)).2.1 x₀.1.2.1 x₀.1.2.2
      (s1R Hb x₀ s))
    (tK (A.keyOf (x₀.2, g) (Γ, s.2)) (A.keyOf (x₀.2, g) (Γ, s.2)).2.2 ref₁ r₁ o1) (x₀.2, g) s.2

variable {A Qk Qr}
variable {i3 i2 i5 iE : ℕ} (hk : ConsP Qk fun t : TbP R => A.keyOf t.1 t.2)
  (hck : CardP Qk i3 i2 i5 iE)
  (hr : ∀ t₀ t₁, ConsP (Qr t₀ t₁) fun t : TbP R => A.respOf t₀ t₁ t.1 t.2)
  (hcr : ∀ t₀ t₁, CardP (Qr t₀ t₁) i3 i2 i5 iE)
include hk hck hr hcr

lemma mixQ_card (t₀ t₁ : Bytes) (sl : SlP) (s₂ : Tab5F × (Blk → R)) :
    (AdversaryRA.mixQ Qk Qr Γ t₀ t₁ sl s₂).card ≤ i2 + i2 :=
  (card_union_le _ _).trans (add_le_add (hck _).2.2.1 (hcr t₀ t₁ _).2.2.1)

lemma qf0_rd3 (ref₀ : Coins refresherBytes) (r₀ : Coins uovM) (x₁ : XR) (o1 : ByteArray × ByteArray)
    (s : ShP R) : Rd3 (fun g => qf0 Hb A Qk Qr Γ ref₀ r₀ x₁ o1 g s) (i3 + i3) :=
  Rd3.bind' (m := fun g => (Qk ((g, x₁.2), (Γ, s.2)), A.keyOf (g, x₁.2) (Γ, s.2)))
    (f := fun qP g => qP.1.2.1 ∪ (Qr (tK qP.2 qP.2.2.1 ref₀ r₀ o1)
      (tK qP.2 qP.2.2.2 x₁.1.2.1 x₁.1.2.2 (s1R Hb x₁ s)) ((g, x₁.2), (Γ, s.2))).2.1)
    (fun _ => rfl) (hk.rd30 hck x₁.2 (Γ, s.2)) fun qP =>
      ((hr _ _).rd30 (hcr _ _) x₁.2 (Γ, s.2)).map fun b => qP.1.2.1 ∪ b.1.2.1

lemma qf0_rd5 (ref₀ : Coins refresherBytes) (r₀ : Coins uovM) (x₁ : XR) (o1 : ByteArray × ByteArray)
    (g : Tab3) : Rd5 (fun s => qf0 Hb A Qk Qr Γ ref₀ r₀ x₁ o1 g s) (i5 + 624 + i5) :=
  Rd5.bind' (m := fun s : ShP R => ((Qk ((g, x₁.2), (Γ, s.2)), A.keyOf (g, x₁.2) (Γ, s.2)),
      s1R Hb x₁ s))
    (f := fun qPy s => qPy.1.1.2.1 ∪ (Qr (tK qPy.1.2 qPy.1.2.2.1 ref₀ r₀ o1)
      (tK qPy.1.2 qPy.1.2.2.2 x₁.1.2.1 x₁.1.2.2 qPy.2) ((g, x₁.2), (Γ, s.2))).2.1)
    (fun _ => rfl) ((hk.rd5 hck (g, x₁.2) Γ).bind fun qP => (s1R_rd5 Hb x₁).map fun y => (qP, y))
    fun qPy => ((hr _ _).rd5 (hcr _ _) (g, x₁.2) Γ).map fun b => qPy.1.1.2.1 ∪ b.1.2.1

lemma qf0_rdE (hHb : HashesWF Hb) (ref₀ : Coins refresherBytes) (r₀ : Coins uovM) (x₁ : XR)
    (o1 : ByteArray × ByteArray) (g : Tab3) :
    RdE (fun s => qf0 Hb A Qk Qr Γ ref₀ r₀ x₁ o1 g s) (iE + 4607 + iE) :=
  RdE.bind' (m := fun s : ShP R => ((Qk ((g, x₁.2), (Γ, s.2)), A.keyOf (g, x₁.2) (Γ, s.2)),
      s1R Hb x₁ s))
    (f := fun qPy s => qPy.1.1.2.1 ∪ (Qr (tK qPy.1.2 qPy.1.2.2.1 ref₀ r₀ o1)
      (tK qPy.1.2 qPy.1.2.2.2 x₁.1.2.1 x₁.1.2.2 qPy.2) ((g, x₁.2), (Γ, s.2))).2.1)
    (fun _ => rfl)
    ((hk.rdE hck (g, x₁.2) Γ).bind fun qP => (s1R_rdE Hb hHb x₁).map fun y => (qP, y))
    fun qPy => ((hr _ _).rdE (hcr _ _) (g, x₁.2) Γ).map fun b => qPy.1.1.2.1 ∪ b.1.2.1

lemma qf1_rd3 (ref₁ : Coins refresherBytes) (r₁ : Coins uovM) (x₀ : XR) (o1 : ByteArray × ByteArray)
    (s : ShP R) : Rd3 (fun g => qf1 Hb A Qk Qr Γ ref₁ r₁ x₀ o1 g s) (i3 + i3) :=
  Rd3.bind' (m := fun g => (Qk ((x₀.2, g), (Γ, s.2)), A.keyOf (x₀.2, g) (Γ, s.2)))
    (f := fun qP g => qP.1.2.1 ∪ (Qr (tK qP.2 qP.2.2.1 x₀.1.2.1 x₀.1.2.2 (s1R Hb x₀ s))
      (tK qP.2 qP.2.2.2 ref₁ r₁ o1) ((x₀.2, g), (Γ, s.2))).2.1)
    (fun _ => rfl) (hk.rd31 hck x₀.2 (Γ, s.2)) fun qP =>
      ((hr _ _).rd31 (hcr _ _) x₀.2 (Γ, s.2)).map fun b => qP.1.2.1 ∪ b.1.2.1

lemma qf1_rd5 (ref₁ : Coins refresherBytes) (r₁ : Coins uovM) (x₀ : XR) (o1 : ByteArray × ByteArray)
    (g : Tab3) : Rd5 (fun s => qf1 Hb A Qk Qr Γ ref₁ r₁ x₀ o1 g s) (i5 + 624 + i5) :=
  Rd5.bind' (m := fun s : ShP R => ((Qk ((x₀.2, g), (Γ, s.2)), A.keyOf (x₀.2, g) (Γ, s.2)),
      s1R Hb x₀ s))
    (f := fun qPy s => qPy.1.1.2.1 ∪ (Qr (tK qPy.1.2 qPy.1.2.2.1 x₀.1.2.1 x₀.1.2.2 qPy.2)
      (tK qPy.1.2 qPy.1.2.2.2 ref₁ r₁ o1) ((x₀.2, g), (Γ, s.2))).2.1)
    (fun _ => rfl) ((hk.rd5 hck (x₀.2, g) Γ).bind fun qP => (s1R_rd5 Hb x₀).map fun y => (qP, y))
    fun qPy => ((hr _ _).rd5 (hcr _ _) (x₀.2, g) Γ).map fun b => qPy.1.1.2.1 ∪ b.1.2.1

lemma qf1_rdE (hHb : HashesWF Hb) (ref₁ : Coins refresherBytes) (r₁ : Coins uovM) (x₀ : XR)
    (o1 : ByteArray × ByteArray) (g : Tab3) :
    RdE (fun s => qf1 Hb A Qk Qr Γ ref₁ r₁ x₀ o1 g s) (iE + 4607 + iE) :=
  RdE.bind' (m := fun s : ShP R => ((Qk ((x₀.2, g), (Γ, s.2)), A.keyOf (x₀.2, g) (Γ, s.2)),
      s1R Hb x₀ s))
    (f := fun qPy s => qPy.1.1.2.1 ∪ (Qr (tK qPy.1.2 qPy.1.2.2.1 x₀.1.2.1 x₀.1.2.2 qPy.2)
      (tK qPy.1.2 qPy.1.2.2.2 ref₁ r₁ o1) ((x₀.2, g), (Γ, s.2))).2.1)
    (fun _ => rfl)
    ((hk.rdE hck (x₀.2, g) Γ).bind fun qP => (s1R_rdE Hb hHb x₀).map fun y => (qP, y))
    fun qPy => ((hr _ _).rdE (hcr _ _) (x₀.2, g) Γ).map fun b => qPy.1.1.2.1 ∪ b.1.2.1

omit hk hck hr hcr in
lemma qf0_h2 (ref₀ : Coins refresherBytes) (r₀ : Coins uovM) (x₁ : XR) (o1 : ByteArray × ByteArray)
    (g : Tab3) (s : ShP R) (G2 : Tab2G pP) :
    qf0 Hb A Qk Qr Γ ref₀ r₀ x₁ o1 g (G2, s.2) = qf0 Hb A Qk Qr Γ ref₀ r₀ x₁ o1 g s := by
  unfold qf0
  rw [s1R_h23]

omit hk hck hr hcr in
lemma qf1_h2 (ref₁ : Coins refresherBytes) (r₁ : Coins uovM) (x₀ : XR) (o1 : ByteArray × ByteArray)
    (g : Tab3) (s : ShP R) (G2 : Tab2G pP) :
    qf1 Hb A Qk Qr Γ ref₁ r₁ x₀ o1 g (G2, s.2) = qf1 Hb A Qk Qr Γ ref₁ r₁ x₀ o1 g s := by
  unfold qf1
  rw [s1R_h23]

end QF

/-! ## The collision term -/

section Bad

variable {Hb : Hashes} {A : AdversaryRA R} {Qk : TbP R → RSP} {Qr : Bytes → Bytes → TbP R → RSP}

/-- A real session's step-1 output is `o1R2` at its seed. -/
lemma s1R_eq_o1R2 (hHb : HashesWF Hb) (A' : AdversaryRO R) (x : XR) (s : ShP R) :
    s1R Hb x s = o1R2 Hb (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2)) ((x.1.1, x.2), s) :=
  @realRun2_out1 (icPrg (rowFn s.2.2)) Hb (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2))
    (kOf A' (A'.msg false) x.1.2.1 x.1.2.2 false []) hHb (hyp2_kOf _ _ _ _ _ _) x.2 s.1 s.2.1 x.1.1

/-- A real session with its continuation's other request fixed. -/
lemma oR_fix (A' : AdversaryRO R) (msg : Bytes) (i : Bool) (x : XR) (t' : ShP R → Bytes)
    (s₂ : Tab5F × (Blk → R)) (G2 G2' : Tab2G pP) (ht : t' (G2', s₂) = t' (G2, s₂)) :
    oR Hb A' msg i x t' (G2', s₂) =
      @realRun2 (icPrg (rowFn s₂.2)) (recH Hb (st1 (stOf x.1.2.1)) (toBA (List.ofFn x.1.2.2)) x.2 G2'
        s₂.1) CrtGen.tables (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2))
        (kOf A' msg x.1.2.1 x.1.2.2 i (t' (G2, s₂))) (ba x.1.1) := by
  rw [oR_cont Hb A' msg i x (G2', s₂) (t₂ := fun _ => t' (G2, s₂)) ht]
  rfl

/-- **A run that reads `H₂³` differently on the patched table reads it at a patched key of its
grinding block.** -/
lemma run_patch_mem (hHb : HashesWF Hb) (A' : AdversaryRO R) (msg : Bytes) (i : Bool) (x : XR)
    (t : Bytes) (s₂ : Tab5F × (Blk → R)) (P : Finset (K2 pP)) (Γ G2 : Tab2G pP)
    (h : @realRun2 (icPrg (rowFn s₂.2)) (recH Hb (st1 (stOf x.1.2.1)) (toBA (List.ofFn x.1.2.2)) x.2
        (patchT P Γ G2) s₂.1) CrtGen.tables (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2))
        (kOf A' msg x.1.2.1 x.1.2.2 i t) (ba x.1.1) ≠
      @realRun2 (icPrg (rowFn s₂.2)) (recH Hb (st1 (stOf x.1.2.1)) (toBA (List.ofFn x.1.2.2)) x.2 G2
        s₂.1) CrtGen.tables (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2))
        (kOf A' msg x.1.2.1 x.1.2.2 i t) (ba x.1.1)) :
    (kOf A' msg x.1.2.1 x.1.2.2 i t (@out1 (icPrg (rowFn s₂.2)) (rec5 Hb s₂.1) CrtGen.tables
        (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2)) (splitSeed (x.2 x.1.1)))).isSome ∧
      ∃ κ ∈ P, κ.1 = blk (preLen pP) (@pre2 (icPrg (rowFn s₂.2)) (rec5 Hb s₂.1) CrtGen.tables
        (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2)) (kOf A' msg x.1.2.1 x.1.2.2 i t)
        (splitSeed (x.2 x.1.1))) := by
  classical
  by_contra hn
  refine h (@realRun2_h23_congr (icPrg (rowFn s₂.2)) Hb (stOf x.1.2.1) (toBA (List.ofFn x.1.2.2))
    _ hHb (hyp2_kOf _ _ _ _ _ _) x.2 G2 _ s₂.1 x.1.1 fun hk c => ?_)
  by_contra hc
  refine hn ⟨hk, key2 pP (@pre2 (icPrg (rowFn s₂.2)) (rec5 Hb s₂.1) CrtGen.tables (stOf x.1.2.1)
    (toBA (List.ofFn x.1.2.2)) (kOf A' msg x.1.2.1 x.1.2.2 i t) (splitSeed (x.2 x.1.1))) c, ?_, rfl⟩
  by_contra hP
  exact hc (patchT_of_not_mem _ _ hP)

end Bad

/-! ## The collision term, bounded -/

section BadBound

variable (Hb : Hashes) (A : AdversaryRA R) (Qk : TbP R → RSP) (Qr : Bytes → Bytes → TbP R → RSP)

/-- **Session `0`'s collision.** -/
def bad0H (c : CH R) (Γ G2 : Tab2G pP) : Prop :=
  oR Hb (A.at (slH c) (Γ, c.2)) ((A.at (slH c) (Γ, c.2)).msg false) false c.1.1
      (tR Hb (A.at (slH c) (Γ, c.2)) ((A.at (slH c) (Γ, c.2)).msg true) c.1.2)
      (patchT (readH Hb A Qk Qr c Γ) Γ G2, c.2) ≠
    oR Hb (A.at (slH c) (Γ, c.2)) ((A.at (slH c) (Γ, c.2)).msg false) false c.1.1
      (tR Hb (A.at (slH c) (Γ, c.2)) ((A.at (slH c) (Γ, c.2)).msg true) c.1.2) (G2, c.2)

/-- **Session `1`'s collision.** -/
def bad1H (c : CH R) (Γ G2 : Tab2G pP) : Prop :=
  oR Hb (A.at (slH c) (Γ, c.2)) ((A.at (slH c) (Γ, c.2)).msg true) true c.1.2
      (tR Hb (A.at (slH c) (Γ, c.2)) ((A.at (slH c) (Γ, c.2)).msg false) c.1.1)
      (patchT (readH Hb A Qk Qr c Γ) Γ G2, c.2) ≠
    oR Hb (A.at (slH c) (Γ, c.2)) ((A.at (slH c) (Γ, c.2)).msg true) true c.1.2
      (tR Hb (A.at (slH c) (Γ, c.2)) ((A.at (slH c) (Γ, c.2)).msg false) c.1.1) (G2, c.2)

lemma badH_iff (c : CH R) (Γ G2 : Tab2G pP) :
    badH Hb A Qk Qr c Γ G2 ↔ bad0H Hb A Qk Qr c Γ G2 ∨ bad1H Hb A Qk Qr c Γ G2 := Iff.rfl

variable {Hb A Qk Qr}

/-- **Session `0`'s collision is the event of `pr_tail2A`**, for session `0`'s continuation and
read set at the Issuer with `H₂³` substituted. -/
lemma bad0_event (hHb : HashesWF Hb) (ref₀ : Coins refresherBytes) (r₀ : Coins uovM) (x₁ : XR)
    (Γ : Tab2G pP) (ρ : Bytes 16) (g : Tab3) (G2 : Tab2G pP) (s₂ : Tab5F × (Blk → R))
    (hb : bad0H Hb A Qk Qr ((((ρ, ref₀, r₀), g), x₁), s₂) Γ G2) :
    (K0 Hb (A.subst Qk Qr Γ) ref₀ r₀ x₁ g (G2, s₂)
        (o1R2 Hb (stOf ref₀) (toBA (List.ofFn r₀)) ((ρ, g), (G2, s₂)))).isSome ∧
      ∃ κ ∈ qf0 Hb A Qk Qr Γ ref₀ r₀ x₁
          (o1R2 Hb (stOf ref₀) (toBA (List.ofFn r₀)) ((ρ, g), (G2, s₂))) g (G2, s₂),
        κ.1 = blk (preLen pP) (preR2 Hb (stOf ref₀) (toBA (List.ofFn r₀))
          (K0 Hb (A.subst Qk Qr Γ) ref₀ r₀ x₁) ((ρ, g), (G2, s₂))) := by
  unfold bad0H at hb
  simp only [slH] at hb
  have ht : tR Hb (A.at (g, x₁.2) (Γ, s₂)) ((A.at (g, x₁.2) (Γ, s₂)).msg true) x₁
      (patchT (readH Hb A Qk Qr ((((ρ, ref₀, r₀), g), x₁), s₂) Γ) Γ G2, s₂) =
      tR Hb (A.at (g, x₁.2) (Γ, s₂)) ((A.at (g, x₁.2) (Γ, s₂)).msg true) x₁ (G2, s₂) := by
    unfold tR
    rw [s1R_h23 Hb x₁ (G2, s₂)]
  rw [oR_fix _ _ _ _ _ s₂ G2 _ ht, oR_fix _ _ _ _ _ s₂ G2 G2 rfl] at hb
  obtain ⟨hk1, κ, hκ, hblk⟩ := run_patch_mem hHb _ _ false (((ρ, ref₀, r₀), g)) _ s₂ _ Γ G2 hb
  have ho : o1R2 Hb (stOf ref₀) (toBA (List.ofFn r₀)) ((ρ, g), (G2, s₂)) =
      s1R Hb (((ρ, ref₀, r₀), g)) (Γ, s₂) :=
    (s1R_eq_o1R2 hHb (A.at (g, x₁.2) (Γ, s₂)) (((ρ, ref₀, r₀), g)) (G2, s₂)).symm.trans
      (s1R_h23 Hb _ (Γ, s₂) G2)
  have hq : qf0 Hb A Qk Qr Γ ref₀ r₀ x₁
      (o1R2 Hb (stOf ref₀) (toBA (List.ofFn r₀)) ((ρ, g), (G2, s₂))) g (G2, s₂) =
      readH Hb A Qk Qr ((((ρ, ref₀, r₀), g), x₁), s₂) Γ := by
    rw [ho]
    unfold qf0 readH tqH
    rw [s1R_h23 Hb x₁ (Γ, s₂) G2]
    rfl
  refine ⟨hk1, κ, ?_, hblk⟩
  rw [hq]
  exact hκ

/-- **Session `1`'s collision is the event of `pr_tail2A`**, for session `1`'s continuation with
session `0` real (`K1R`) and its read set. -/
lemma bad1_event (hHb : HashesWF Hb) (ref₁ : Coins refresherBytes) (r₁ : Coins uovM) (x₀ : XR)
    (Γ : Tab2G pP) (ρ : Bytes 16) (g : Tab3) (G2 : Tab2G pP) (s₂ : Tab5F × (Blk → R))
    (hb : bad1H Hb A Qk Qr ((x₀, ((ρ, ref₁, r₁), g)), s₂) Γ G2) :
    (K1R Hb (A.subst Qk Qr Γ) ref₁ r₁ x₀ g (G2, s₂)
        (o1R2 Hb (stOf ref₁) (toBA (List.ofFn r₁)) ((ρ, g), (G2, s₂)))).isSome ∧
      ∃ κ ∈ qf1 Hb A Qk Qr Γ ref₁ r₁ x₀
          (o1R2 Hb (stOf ref₁) (toBA (List.ofFn r₁)) ((ρ, g), (G2, s₂))) g (G2, s₂),
        κ.1 = blk (preLen pP) (preR2 Hb (stOf ref₁) (toBA (List.ofFn r₁))
          (K1R Hb (A.subst Qk Qr Γ) ref₁ r₁ x₀) ((ρ, g), (G2, s₂))) := by
  unfold bad1H at hb
  simp only [slH] at hb
  have ht : tR Hb (A.at (x₀.2, g) (Γ, s₂)) ((A.at (x₀.2, g) (Γ, s₂)).msg false) x₀
      (patchT (readH Hb A Qk Qr ((x₀, ((ρ, ref₁, r₁), g)), s₂) Γ) Γ G2, s₂) =
      tR Hb (A.at (x₀.2, g) (Γ, s₂)) ((A.at (x₀.2, g) (Γ, s₂)).msg false) x₀ (G2, s₂) := by
    unfold tR
    rw [s1R_h23 Hb x₀ (G2, s₂)]
  rw [oR_fix _ _ _ _ _ s₂ G2 _ ht, oR_fix _ _ _ _ _ s₂ G2 G2 rfl] at hb
  obtain ⟨hk1, κ, hκ, hblk⟩ := run_patch_mem hHb _ _ true (((ρ, ref₁, r₁), g)) _ s₂ _ Γ G2 hb
  have ho : o1R2 Hb (stOf ref₁) (toBA (List.ofFn r₁)) ((ρ, g), (G2, s₂)) =
      s1R Hb (((ρ, ref₁, r₁), g)) (Γ, s₂) :=
    (s1R_eq_o1R2 hHb (A.at (x₀.2, g) (Γ, s₂)) (((ρ, ref₁, r₁), g)) (G2, s₂)).symm.trans
      (s1R_h23 Hb _ (Γ, s₂) G2)
  have hq : qf1 Hb A Qk Qr Γ ref₁ r₁ x₀
      (o1R2 Hb (stOf ref₁) (toBA (List.ofFn r₁)) ((ρ, g), (G2, s₂))) g (G2, s₂) =
      readH Hb A Qk Qr ((x₀, ((ρ, ref₁, r₁), g)), s₂) Γ := by
    rw [ho]
    unfold qf1 readH tqH
    rw [s1R_h23 Hb x₀ (Γ, s₂) G2]
    rfl
  refine ⟨hk1, κ, ?_, hblk⟩
  rw [hq]
  exact hκ

end BadBound

/-! ## The collision probabilities -/

section BadPr

variable {Hb : Hashes} {A : AdversaryRA R} {Qk : TbP R → RSP} {Qr : Bytes → Bytes → TbP R → RSP}

/-- Regroup the resampled game's tape around session `0`'s run. -/
def eqB0 : (Tab2G pP × ((Coins refresherBytes × Coins uovM) × XR)) × ((Bytes 16 × Tab3) × ShP R) ≃
    (CH R × Tab2G pP) × Tab2G pP where
  toFun w := ((((((w.2.1.1, w.1.2.1.1, w.1.2.1.2), w.2.1.2), w.1.2.2), w.2.2.2), w.1.1), w.2.2.1)
  invFun v := ((v.1.2, ((v.1.1.1.1.1.2.1, v.1.1.1.1.1.2.2), v.1.1.1.2)),
    ((v.1.1.1.1.1.1, v.1.1.1.1.2), (v.2, v.1.1.2)))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Regroup the resampled game's tape around session `1`'s run. -/
def eqB1 : (Tab2G pP × (XR × (Coins refresherBytes × Coins uovM))) × ((Bytes 16 × Tab3) × ShP R) ≃
    (CH R × Tab2G pP) × Tab2G pP where
  toFun w := ((((w.1.2.1, ((w.2.1.1, w.1.2.2.1, w.1.2.2.2), w.2.1.2)), w.2.2.2), w.1.1), w.2.2.1)
  invFun v := ((v.1.2, (v.1.1.1.1, (v.1.1.1.2.1.2.1, v.1.1.1.2.1.2.2))),
    ((v.1.1.1.2.1.1, v.1.1.1.2.2), (v.2, v.1.1.2)))
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The collision error of one session**: `pr_tail2A` at the budgets of the continuation and the
read set (`2⁻¹¹³ + εz(6i₃, 6i₅ + 2184, 6i_E + 18428) + 2i₂·2⁻¹²⁸`). -/
noncomputable def εcol (R : Type) [Fintype R] [CipherRow R] [ZKRow R] (i3 i2 i5 iE : ℕ) : ℝ :=
  1 / 2 ^ 113 + ZKRow.εz R pP (6 * i3) (6 * i5 + 2184) (6 * iE + 18428) + (i2 + i2 : ℕ) / 2 ^ 128

variable {i3 i2 i5 iE : ℕ} (hHb : HashesWF Hb) (hk : ConsP Qk fun t : TbP R => A.keyOf t.1 t.2)
  (hck : CardP Qk i3 i2 i5 iE)
  (hr : ∀ t₀ t₁, ConsP (Qr t₀ t₁) fun t : TbP R => A.respOf t₀ t₁ t.1 t.2)
  (hcr : ∀ t₀ t₁, CardP (Qr t₀ t₁) i3 i2 i5 iE)
include hHb hk hck hr hcr

/-- **Session `0`'s collision probability.** -/
theorem pr_bad0H [ZKRow R] [ZK2ARow R] :
    pr ((CH R × Tab2G pP) × Tab2G pP) (fun w => bad0H Hb A Qk Qr w.1.1 w.1.2 w.2) ≤
      εcol R i3 i2 i5 iE := by
  rw [← pr_equiv eqB0]
  refine pr_le_of_fst fun ζ => ?_
  obtain ⟨Γ, ⟨ref₀, r₀⟩, x₁⟩ := ζ
  have hI := AdversaryRA.IBudget.subst hk hck hr hcr Γ
  have hh := hyp2RA_R hHb hI ref₀ r₀ x₁
  have h := pr_tail2A Hb (stOf ref₀) (toBA (List.ofFn r₀)) uovM
    (K0 Hb (A.subst Qk Qr Γ) ref₀ r₀ x₁) hh hHb (smallParams_of_le (p := pP) (by decide) (by decide))
    (qf0 Hb A Qk Qr Γ ref₀ r₀ x₁) (fun o1 g s G2 => qf0_h2 Hb Γ ref₀ r₀ x₁ o1 g s G2)
    (fun o1 g s => mixQ_card Γ hk hck hr hcr _ _ _ _)
    (qf0_rd3 Hb Γ hk hck hr hcr ref₀ r₀ x₁) (qf0_rd5 Hb Γ hk hck hr hcr ref₀ r₀ x₁)
    (qf0_rdE Hb Γ hk hck hr hcr hHb ref₀ r₀ x₁)
  refine le_trans (pr_mono fun a hb => ?_) (h.trans ?_)
  · obtain ⟨⟨ρ, g⟩, G2, s₂⟩ := a
    exact bad0_event hHb ref₀ r₀ x₁ Γ ρ g G2 s₂ hb
  · have m := ZKRow.εz_mono (R := R) pP
      (q3 := i3 + i3 + (i3 + i3) + (i3 + i3)) (q3' := 6 * i3)
      (q5 := i5 + 624 + i5 + (i5 + 624 + i5) + 312 + (i5 + 624 + i5)) (q5' := 6 * i5 + 2184)
      (qE := iE + 4607 + iE + (iE + 4607 + iE) + 4607 + (iE + 4607 + iE)) (qE' := 6 * iE + 18428)
      (by omega) (by omega) (by omega)
    unfold εcol
    show 1 / 2 ^ 113 + ZKRow.εz R pP _ _ _ + ((i2 + i2 : ℕ) : ℝ) / 2 ^ 128 ≤ _
    linarith

/-- **Session `1`'s collision probability.** -/
theorem pr_bad1H [ZKRow R] [ZK2ARow R] :
    pr ((CH R × Tab2G pP) × Tab2G pP) (fun w => bad1H Hb A Qk Qr w.1.1 w.1.2 w.2) ≤
      εcol R i3 i2 i5 iE := by
  rw [← pr_equiv eqB1]
  refine pr_le_of_fst fun ζ => ?_
  obtain ⟨Γ, x₀, ref₁, r₁⟩ := ζ
  have hI := AdversaryRA.IBudget.subst hk hck hr hcr Γ
  have hh := hyp2RA_R1 Hb hHb hI ref₁ r₁ x₀
  have h := pr_tail2A Hb (stOf ref₁) (toBA (List.ofFn r₁)) uovM
    (K1R Hb (A.subst Qk Qr Γ) ref₁ r₁ x₀) hh hHb (smallParams_of_le (p := pP) (by decide) (by decide))
    (qf1 Hb A Qk Qr Γ ref₁ r₁ x₀) (fun o1 g s G2 => qf1_h2 Hb Γ ref₁ r₁ x₀ o1 g s G2)
    (fun o1 g s => mixQ_card Γ hk hck hr hcr _ _ _ _)
    (qf1_rd3 Hb Γ hk hck hr hcr ref₁ r₁ x₀) (qf1_rd5 Hb Γ hk hck hr hcr ref₁ r₁ x₀)
    (qf1_rdE Hb Γ hk hck hr hcr hHb ref₁ r₁ x₀)
  refine le_trans (pr_mono fun a hb => ?_) (h.trans ?_)
  · obtain ⟨⟨ρ, g⟩, G2, s₂⟩ := a
    exact bad1_event hHb ref₁ r₁ x₀ Γ ρ g G2 s₂ hb
  · have m := ZKRow.εz_mono (R := R) pP
      (q3 := i3 + i3 + (i3 + i3) + (i3 + i3)) (q3' := 6 * i3)
      (q5 := i5 + 624 + i5 + (i5 + 624 + i5) + 312 + (i5 + 624 + i5)) (q5' := 6 * i5 + 2184)
      (qE := iE + 4607 + iE + (iE + 4607 + iE) + 4607 + (iE + 4607 + iE)) (qE' := 6 * iE + 18428)
      (by omega) (by omega) (by omega)
    unfold εcol
    show 1 / 2 ^ 113 + ZKRow.εz R pP _ _ _ + ((i2 + i2 : ℕ) : ℝ) / 2 ^ 128 ≤ _
    linarith

end BadPr

/-! ## One world -/

section World

variable {Hb : Hashes} {A : AdversaryRA R} {Qk : TbP R → RSP} {Qr : Bytes → Bytes → TbP R → RSP}

/-- Regroup the resampled game's tape as `Γ` and the game's tape. -/
def eqW : (CH R × Tab2G pP) × Tab2G pP ≃ Tab2G pP × ((XR × XR) × ShP R) where
  toFun v := (v.1.2, zH v.1.1 v.2)
  invFun w := (((w.2.1, w.2.2.2), w.1), w.2.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The collision term of one world**: `0` if the interaction does not read `H₂³`, else the
two sessions' `εcol`. -/
noncomputable def h23W (R : Type) [Fintype R] [CipherRow R] [ZKRow R] (i3 i2 i5 iE : ℕ) : ℝ :=
  if i2 = 0 then 0 else 2 * εcol R i3 i2 i5 iE

variable {i3 i2 i5 iE : ℕ} (hHb : HashesWF Hb) (hk : ConsP Qk fun t : TbP R => A.keyOf t.1 t.2)
  (hck : CardP Qk i3 i2 i5 iE)
  (hr : ∀ t₀ t₁, ConsP (Qr t₀ t₁) fun t : TbP R => A.respOf t₀ t₁ t.1 t.2)
  (hcr : ∀ t₀ t₁, CardP (Qr t₀ t₁) i3 i2 i5 iE)
include hHb hk hck hr hcr

/-- **World `false`, the interaction's `H₂³` reads taken out**: the game is, up to the collision
term, the game of the Issuer with `H₂³` substituted, averaged over the substituted table. -/
theorem G0RA_subst_close [ZKRow R] [ZK2ARow R] :
    |pr ((XR × XR) × ShP R) (G0RA Hb A) -
        pr (Tab2G pP × ((XR × XR) × ShP R)) (fun w => G0RA Hb (A.subst Qk Qr w.1) w.2)| ≤
      h23W R i3 i2 i5 iE := by
  have hagree : ∀ v : (CH R × Tab2G pP) × Tab2G pP, ¬ badH Hb A Qk Qr v.1.1 v.1.2 v.2 →
      (GF Hb A v.1.1 (intH Hb A v.1.1 v.1.2) (patchT (readH Hb A Qk Qr v.1.1 v.1.2) v.1.2 v.2) ↔
        G0RA Hb (A.subst Qk Qr v.1.2) (zH v.1.1 v.2)) := fun v hv =>
    (GF_iff_at Hb v.1.1 v.1.2 _).trans (G0_at_iff_subst Hb v.1.1 v.1.2 v.2 hv)
  have hab := abs_pr_sub_le_of_agree
    (fun v : (CH R × Tab2G pP) × Tab2G pP =>
      GF Hb A v.1.1 (intH Hb A v.1.1 v.1.2) (patchT (readH Hb A Qk Qr v.1.1 v.1.2) v.1.2 v.2))
    (fun v => G0RA Hb (A.subst Qk Qr v.1.2) (zH v.1.1 v.2))
    (fun v => badH Hb A Qk Qr v.1.1 v.1.2 v.2) hagree
  have e2 : pr (Tab2G pP × ((XR × XR) × ShP R)) (fun w => G0RA Hb (A.subst Qk Qr w.1) w.2) =
      pr ((CH R × Tab2G pP) × Tab2G pP) (fun v => G0RA Hb (A.subst Qk Qr v.1.2) (zH v.1.1 v.2)) :=
    (pr_equiv eqW (fun w => G0RA Hb (A.subst Qk Qr w.1) w.2)).symm
  rw [pr_G0RA_resample Hb hk hr, e2]
  refine hab.trans ?_
  unfold h23W
  split_ifs with h0
  · -- Without `H₂³` reads nothing is patched.
    refine le_of_eq ((pr_congr fun v => iff_false_intro fun hb => ?_).trans pr_false)
    have hc : readH Hb A Qk Qr v.1.1 v.1.2 = ∅ := by
      have := mixQ_card v.1.2 hk hck hr hcr (tqH Hb A v.1.1 v.1.2).1 (tqH Hb A v.1.1 v.1.2).2
        (slH v.1.1) v.1.1.2
      rw [h0] at this
      exact Finset.card_eq_zero.1 (Nat.le_zero.1 this)
    have hp : patchT (readH Hb A Qk Qr v.1.1 v.1.2) v.1.2 v.2 = v.2 := by
      rw [hc]; funext κ; exact patchT_of_not_mem _ _ (Finset.notMem_empty κ)
    rcases (badH_iff Hb A Qk Qr _ _ _).1 hb with h | h
    · exact h (by rw [hp])
    · exact h (by rw [hp])
  · rw [pr_congr fun v : (CH R × Tab2G pP) × Tab2G pP => badH_iff Hb A Qk Qr v.1.1 v.1.2 v.2]
    have h0' := pr_bad0H hHb hk hck hr hcr
    have h1' := pr_bad1H hHb hk hck hr hcr
    have := pr_or_le (fun v : (CH R × Tab2G pP) × Tab2G pP => bad0H Hb A Qk Qr v.1.1 v.1.2 v.2)
      (fun v => bad1H Hb A Qk Qr v.1.1 v.1.2 v.2)
    linarith

end World

/-! ## Blindness -/

section Blind

/-- **The collision term of the bound**: `0` if the interaction does not read `H₂³`, else four
times `εcol` (two sessions, two worlds):
`4·(2⁻¹¹³ + εz(pP; 6i₃, 6i₅ + 2184, 6i_E + 18428) + 2i₂·2⁻¹²⁸)`. -/
noncomputable def h23H (R : Type) [Fintype R] [CipherRow R] [ZKRow R] (i3 i2 i5 iE : ℕ) : ℝ :=
  if i2 = 0 then 0 else 4 * εcol R i3 i2 i5 iE

lemma two_h23W [ZKRow R] (i3 i2 i5 iE : ℕ) :
    h23W R i3 i2 i5 iE + h23W R i3 i2 i5 iE = h23H R i3 i2 i5 iE := by
  unfold h23W h23H
  split_ifs <;> ring

/-- **The joint budget of the Issuer with the roles exchanged.** -/
lemma AdversaryRA.IBudgetH.swap {A : AdversaryRA R} {i3 i2 i5 iE : ℕ} (h : A.IBudgetH i3 i2 i5 iE) :
    A.swap.IBudgetH i3 i2 i5 iE := by
  obtain ⟨Qk, hk, hck⟩ := h.k
  refine ⟨⟨_, AdversaryRA.consP_swapK hk, AdversaryRA.cardP_swap hck⟩, fun t₀ t₁ => ?_⟩
  obtain ⟨Qr, hr, hcr⟩ := h.r t₁ t₀
  refine ⟨fun t => AdversaryRA.swapRS (Qr ((t.1.2, t.1.1), t.2)), fun t t' ⟨h1, h2, h3, h4, h5⟩ => ?_,
    AdversaryRA.cardP_swap hcr⟩
  obtain ⟨e1, e2⟩ := hr ((t.1.2, t.1.1), t.2) ((t'.1.2, t'.1.1), t'.2) ⟨h2, h1, h3, h4, h5⟩
  exact ⟨by simp only [e1], Prod.ext (congrArg Prod.snd e2) (congrArg Prod.fst e2)⟩

/-- **PomFRIT blindness with an Issuer whose interaction reads every table, `H₂³` included**
(ROM and ideal cipher, label rows, the Lean prover on the shared tables, SHAKE as the base record,
for every type of cipher rows): the guess reads `(q₃, q₅, q_E)` keys and `H₂³` freely; the key
stage and the response stage read, jointly in both slices and the shared tables, at most `i₃` keys
of each slice, `i₂` `H₂³` keys, `i₅` `H₅` keys and `i_E` cipher keys (`IBudgetH`):

    |Pr[W₀] − Pr[W₁]| ≤ 4·εz(pP; q₃ + 6i₃, q₅ + 6i₅ + 1872, q_E + 6i_E + 23035)
                         + 2·noHitProb + 2·2⁻¹²⁸ + h23H(i₃, i₂, i₅, i_E). -/
theorem blindnessRAH_lean_numG [ZKRow R] [ZK2ARow R] (A : AdversaryRA R) {q3 q5 qE i3 i2 i5 iE : ℕ}
    (hA : A.GBudget q3 q5 qE) (hI : A.IBudgetH i3 i2 i5 iE) :
    |pr ((XR × XR) × ShP R) (realGameRA Hashes.shake A false) -
        pr ((XR × XR) × ShP R) (realGameRA Hashes.shake A true)| ≤
      4 * ZKRow.εz R pP (q3 + 6 * i3) (q5 + 6 * i5 + 1872) (qE + 6 * iE + 23035) + 2 * noHitProb +
        2 / 2 ^ 128 + h23H R i3 i2 i5 iE := by
  obtain ⟨Qk, hk, hck⟩ := hI.k
  choose Qr hr hcr using hI.r
  have hk' : ConsP Qk fun t : TbP R => A.keyOf t.1 t.2 := hk
  have hck' : CardP Qk i3 i2 i5 iE := hck
  have hr' : ∀ t₀ t₁, ConsP (Qr t₀ t₁) fun t : TbP R => A.respOf t₀ t₁ t.1 t.2 := hr
  have hcr' : ∀ t₀ t₁, CardP (Qr t₀ t₁) i3 i2 i5 iE := hcr
  have h0 : pr ((XR × XR) × ShP R) (realGameRA Hashes.shake A false) =
      pr ((XR × XR) × ShP R) (G0RA Hashes.shake A) := pr_congr (realGameRA_iff Hashes.shake A)
  have h1 : ∀ A' : AdversaryRA R, pr ((XR × XR) × ShP R) (realGameRA Hashes.shake A' true) =
      pr ((XR × XR) × ShP R) (G0RA Hashes.shake A'.swap) := fun A' =>
    (pr_congr (realGameRA_true Hashes.shake A')).trans
      ((pr_equiv swapXR (realGameRA Hashes.shake A'.swap false)).trans
        (pr_congr (realGameRA_iff Hashes.shake A'.swap)))
  -- World `false` and world `true` (the exchanged Issuer, the exchanged read sets).
  have cA := G0RA_subst_close hashesWF_shake hk' hck' hr' hcr'
  have cS := G0RA_subst_close (A := A.swap) hashesWF_shake (AdversaryRA.consP_swapK hk')
    (AdversaryRA.cardP_swap hck') (AdversaryRA.consP_swapR hr')
    (fun t₀ t₁ => AdversaryRA.cardP_swap (hcr' t₁ t₀))
  -- The substituted Issuers satisfy the hypotheses of `blindnessRA_lean_numG`.
  have hmid : |pr (Tab2G pP × ((XR × XR) × ShP R))
        (fun w => G0RA Hashes.shake (A.subst Qk Qr w.1) w.2) -
      pr (Tab2G pP × ((XR × XR) × ShP R))
        (fun w => G0RA Hashes.shake ((A.subst Qk Qr w.1).swap) w.2)| ≤
      4 * ZKRow.εz R pP (q3 + 6 * i3) (q5 + 6 * i5 + 1872) (qE + 6 * iE + 23035) +
        2 * noHitProb + 2 / 2 ^ 128 := by
    refine abs_pr_prod_sub_le _ _ fun Γ => ?_
    have hb := blindnessRA_lean_numG (A.subst Qk Qr Γ)
      (AdversaryRA.GBudget.subst hA hk' hck' hr' hcr' Γ) (AdversaryRA.IBudget.subst hk' hck' hr' hcr' Γ)
    rw [pr_congr (realGameRA_iff Hashes.shake (A.subst Qk Qr Γ)), h1] at hb
    have m := ZKRow.εz_mono (R := R) pP
      (q3 := i3 + i3 + q3 + 4 * i3) (q3' := q3 + 6 * i3)
      (q5 := i5 + i5 + q5 + 4 * i5 + 1872) (q5' := q5 + 6 * i5 + 1872)
      (qE := iE + iE + qE + 4 * iE + 23035) (qE' := qE + 6 * iE + 23035)
      (by omega) (by omega) (by omega)
    exact hb.trans (by linarith)
  have e : pr (Tab2G pP × ((XR × XR) × ShP R))
        (fun w => G0RA Hashes.shake ((A.subst Qk Qr w.1).swap) w.2) =
      pr (Tab2G pP × ((XR × XR) × ShP R))
        (fun w => G0RA Hashes.shake (A.swap.subst (fun t => AdversaryRA.swapRS (Qk ((t.1.2, t.1.1), t.2)))
          (fun t₀ t₁ t => AdversaryRA.swapRS (Qr t₁ t₀ ((t.1.2, t.1.1), t.2))) w.1) w.2) := by
    simp only [AdversaryRA.swap_subst]
  rw [e] at hmid
  rw [h0, h1, ← two_h23W]
  have t1 := abs_sub_le (pr ((XR × XR) × ShP R) (G0RA Hashes.shake A))
    (pr (Tab2G pP × ((XR × XR) × ShP R)) (fun w => G0RA Hashes.shake (A.subst Qk Qr w.1) w.2))
    (pr ((XR × XR) × ShP R) (G0RA Hashes.shake A.swap))
  have t2 := abs_sub_le
    (pr (Tab2G pP × ((XR × XR) × ShP R)) (fun w => G0RA Hashes.shake (A.subst Qk Qr w.1) w.2))
    (pr (Tab2G pP × ((XR × XR) × ShP R))
        (fun w => G0RA Hashes.shake (A.swap.subst (fun t => AdversaryRA.swapRS (Qk ((t.1.2, t.1.1), t.2)))
          (fun t₀ t₁ t => AdversaryRA.swapRS (Qr t₁ t₀ ((t.1.2, t.1.1), t.2))) w.1) w.2))
    (pr ((XR × XR) × ShP R) (G0RA Hashes.shake A.swap))
  rw [abs_sub_comm (pr _ (G0RA Hashes.shake A.swap))] at cS
  linarith

/-- **PomFRIT blindness with an Issuer whose interaction reads every table, `H₂³` included**
(function rows, every term explicit):

    |Pr[W₀] − Pr[W₁]| ≤ 4·εRO(q₃ + 6i₃, q₅ + 6i₅ + 1872, q_E + 6i_E + 23035)
                         + 2·noHitProb + 2·2⁻¹²⁸
                         + [i₂ > 0]·4·(2⁻¹¹³ + εRO(6i₃, 6i₅ + 2184, 6i_E + 18428) + 2i₂·2⁻¹²⁸). -/
theorem blindnessRAH_lean_num (A : AdversaryRA (Blk → Blk)) {q3 q5 qE i3 i2 i5 iE : ℕ}
    (hA : A.GBudget q3 q5 qE) (hI : A.IBudgetH i3 i2 i5 iE) :
    |pr ((XR × XR) × ShP (Blk → Blk)) (realGameRA Hashes.shake A false) -
        pr ((XR × XR) × ShP (Blk → Blk)) (realGameRA Hashes.shake A true)| ≤
      4 * εRO (q3 + 6 * i3) (q5 + 6 * i5 + 1872) (qE + 6 * iE + 23035) + 2 * noHitProb +
        2 / 2 ^ 128 +
        (if i2 = 0 then 0 else
          4 * (1 / 2 ^ 113 + εRO (6 * i3) (6 * i5 + 2184) (6 * iE + 18428) +
            (i2 + i2 : ℕ) / 2 ^ 128)) :=
  blindnessRAH_lean_numG A hA hI

end Blind

end VoleMole.Privacy.PomFRIT
