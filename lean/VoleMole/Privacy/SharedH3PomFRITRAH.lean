import VoleMole.Privacy.PomFRITRAH
import VoleMole.Privacy.SharedH3PomFRITRA
import VoleMole.ZK.SharedH3Tail

/-!
# PomFRIT blindness with one shared `H₃` and an Issuer whose interaction also reads `H₂³`

`Privacy/PomFRITRAH.lean` (the Issuer's key, messages and responses read every table, `H₂³`
included, under the joint budget `IBudgetH`) in the model of `Privacy/SharedH3PomFRITRA.lean`
(one shared `H₃`: the shared tables carry `H₃`'s columns in their rows, each session reads its
slice at its prefix; the Issuer reads `H₃` through the rows and no slot slice:
`IBudgetH 0 i₂ i₅ i_E`, `GBudget 0 q₅ q_E`).

The proof is `PomFRITRAH.lean`'s, redone on the shared tables:

* *Lazy sampling of `H₂³`* (`pr_G0RASh_resample`): the shared game is the slice game at the
  tape `τR z` (the sessions' slices the columns at their prefixes), and `τR` reads only the rows,
  not `H₂³`; so `pr_resampleC` applies with the coins mapped by `τC`, and world `false` is the
  game in which the interaction reads an independent table `Γ`, the sessions and the guess run on
  `H₂³` patched with `Γ` at the interaction's read set.
* *The substituted Issuer* `A.subst Γ` reads no slot slice and no `H₂³` (`IBudget 0 i₅ i_E`); its
  guess reads `(0, q₅ + 2i₅, q_E + 2i_E)` keys. `blindnessRASh_numG` (one shared `H₃`) applies to
  it for every `Γ`.
* *The collision term* (`pr_bad0HSh`, `pr_bad1HSh`): a real session's grinding block meets the
  interaction's `H₂³` read set; `ZK.Sim.pr_tail2Sh` (two-phase zero knowledge for the prover that
  reads its column, `zk2_sharedA`'s re-sampling, then `pr_tail2A`). The continuation and the read
  set read the other session's column through one more row (`rdE_h3At`):

      εcolSh = 2⁻¹¹³ + εz(pP; 6i_E + 13824, 6i₅ + 2184, 6i_E + 18431) + 2i₂·2⁻¹²⁸.

**`blindnessRAHSh_numG`** (every type of cipher rows), **`blindnessRAHSh_num`** (function rows),
**`blindnessRAHSh_num_perm`** (permutation rows):

    |Pr[W₀] − Pr[W₁]| ≤ 4·εz(pP; q_E + 6i_E + 23035, q₅ + 6i₅ + 1872, q_E + 6i_E + 23035)
                         + 2·noHitProb + 2·2⁻¹²⁸ + [i₂ > 0]·4·εcolSh.

Against `blindnessRAH_lean_num` the slice budgets (`q₃ + 6i₃`, `6i₃`) become row budgets (each
row read is also a read of the replaced session's column), as in `blindnessRASh_num`; no
prefix-collision term.
-/

open Finset

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.PomFRIT

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.ZK.Sim VoleMole.Arith
open VoleMole.Spec VoleMole.Spec.PomFRIT VoleMole.ZK.IC

attribute [local irreducible] commitRefresher UOVKey.eval

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R]

/-! ## Readers that read no slice -/

section Free

variable {X : Type*} {Q : TbP (RowH R) → RSP} {f : TbP (RowH R) → X}

/-- **A joint reader with no slice key** has the same read sets and output at every slices. -/
lemma ConsP.free (hQ : ConsP Q f) {a2 a5 aE : ℕ} (hc : CardP Q 0 a2 a5 aE) (sl sl' : SlP)
    (s : ShP (RowH R)) : Q (sl', s) = Q (sl, s) ∧ f (sl', s) = f (sl, s) := by
  have h1 : (Q (sl, s)).1.1 = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 (hc _).1)
  have h2 : (Q (sl, s)).1.2 = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 (hc _).2.1)
  refine hQ (sl, s) (sl', s) ⟨fun k hk => ?_, fun k hk => ?_, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl⟩
  · rw [h1] at hk; exact absurd hk (Finset.notMem_empty _)
  · rw [h2] at hk; exact absurd hk (Finset.notMem_empty _)

lemma SReadsP.free {a2 a5 aE : ℕ} (h : SReadsP f 0 a2 a5 aE) (sl sl' : SlP) (s : ShP (RowH R)) :
    f (sl', s) = f (sl, s) := by
  obtain ⟨Q, hQ, hc⟩ := h
  exact (ConsP.free hQ hc sl sl' s).2

/-- **The Issuer whose joint budget reads no slice is the same at every pair of slices.** -/
lemma AdversaryRA.at_freeH {A : AdversaryRA (RowH R)} {i2 i5 iE : ℕ} (hI : A.IBudgetH 0 i2 i5 iE)
    (sl sl' : SlP) (s : ShP (RowH R)) : A.at sl s = A.at sl' s :=
  AdversaryRA.at_eq_of (SReadsP.free hI.k sl' sl s) fun t₀ t₁ => SReadsP.free (hI.r t₀ t₁) sl' sl s

variable (Hb : Hashes)

/-- **The shared game is the slice game at the columns** for an Issuer that is the same at every
slices. -/
lemma realGameRASh_iff' {A : AdversaryRA (RowH R)} {q5 qE : ℕ} (hA : A.GBudget 0 q5 qE)
    (hF : ∀ sl sl' s, A.at sl s = A.at sl' s) (b : Bool) (z : (XR × XR) × ShP (RowH R)) :
    realGameRASh Hb A b z ↔ realGameRA Hb A b (τR Hb z) := by
  unfold realGameRASh realGameRA
  rw [realGameSh_iff (AdversaryRA.sliceFree hA _ _)]
  show realGameRO Hb (A.at (z.1.1.2, z.1.2.2) z.2) b (τR Hb z) ↔
    realGameRO Hb (A.at ((τR Hb z).1.1.2, (τR Hb z).1.2.2) z.2) b (τR Hb z)
  rw [hF (z.1.1.2, z.1.2.2) ((τR Hb z).1.1.2, (τR Hb z).1.2.2)]

/-- **World `true` is world `false` of the exchanged Issuer**, in the shared model. -/
lemma pr_realGameRASh_true {A : AdversaryRA (RowH R)} {q5 qE : ℕ} (hA : A.GBudget 0 q5 qE)
    (hF : ∀ sl sl' s, A.at sl s = A.at sl' s) :
    pr ((XR × XR) × ShP (RowH R)) (realGameRASh Hb A true) =
      pr ((XR × XR) × ShP (RowH R)) (fun z => G0RA Hb A.swap (τR Hb z)) := by
  rw [← pr_equiv swapXR (fun z => G0RA Hb A.swap (τR Hb z))]
  refine pr_congr fun z => ?_
  rw [realGameRASh_iff' Hb hA hF, realGameRA_true]
  exact realGameRA_iff Hb A.swap _

end Free

/-! ## Lazy sampling of `H₂³` on the shared tables -/

section Resample

variable (Hb : Hashes) (A : AdversaryRA (RowH R)) (Qk : TbP (RowH R) → RSP)
  (Qr : Bytes → Bytes → TbP (RowH R) → RSP)

/-- **The coins with the sessions' slices replaced by the columns at their prefixes** (`τR` on the
coins; it does not read `H₂³`). -/
noncomputable def τC (c : CH (RowH R)) : CH (RowH R) :=
  (((c.1.1.1, fun j => (c.2.2 j).2 (keyP Hb c.1.1.1.2)),
    (c.1.2.1, fun j => (c.2.2 j).2 (keyP Hb c.1.2.1.2))), c.2)

lemma τR_zH (c : CH (RowH R)) (G2 : Tab2G pP) : τR Hb (zH c G2) = zH (τC Hb c) G2 := rfl

variable {A Qk Qr}

/-- **Lazy sampling of the interaction's `H₂³` reads, one shared `H₃`.** -/
theorem pr_G0RASh_resample (hk : ConsP Qk fun t : TbP (RowH R) => A.keyOf t.1 t.2)
    (hr : ∀ t₀ t₁, ConsP (Qr t₀ t₁) fun t : TbP (RowH R) => A.respOf t₀ t₁ t.1 t.2) :
    pr ((XR × XR) × ShP (RowH R)) (fun z => G0RA Hb A (τR Hb z)) =
      pr ((CH (RowH R) × Tab2G pP) × Tab2G pP) (fun w =>
        GF Hb A (τC Hb w.1.1) (intH Hb A (τC Hb w.1.1) w.1.2)
          (patchT (readH Hb A Qk Qr (τC Hb w.1.1) w.1.2) w.1.2 w.2)) := by
  rw [← pr_equiv eqCH (fun z => G0RA Hb A (τR Hb z))]
  have e : ∀ w : CH (RowH R) × Tab2G pP, G0RA Hb A (τR Hb (eqCH w)) ↔
      GF Hb A (τC Hb w.1) (intH Hb A (τC Hb w.1) w.2) w.2 :=
    fun w => G0_fix Hb A (slH (τC Hb w.1)) (w.2, w.1.2) (zH (τC Hb w.1) w.2)
  rw [pr_congr e]
  exact pr_resampleC (fun P a b => patchT P a b) (fun P a b => ∀ κ ∈ P, a κ = b κ)
    (fun P a b κ hκ => (patchT_of_mem a b hκ).symm) (fun P a b => patchT_patchT_swap P a b)
    (fun c => intH Hb A (τC Hb c)) (fun c => readH Hb A Qk Qr (τC Hb c))
    (fun c t t' h => readH_cons Hb hk hr (τC Hb c) t t' h) (fun c => GF Hb A (τC Hb c))

end Resample

/-! ## The continuations and read sets with the other session's slice its column -/

section Conts

variable {Hb : Hashes} {A : AdversaryRA (RowH R)} {Qk : TbP (RowH R) → RSP}
  {Qr : Bytes → Bytes → TbP (RowH R) → RSP} (Γ : Tab2G pP)

/-- **Session `0`'s read set, session `1`'s slice its column.** -/
noncomputable def qf0Sh (Hb : Hashes) (A : AdversaryRA (RowH R)) (Qk : TbP (RowH R) → RSP)
    (Qr : Bytes → Bytes → TbP (RowH R) → RSP) (Γ : Tab2G pP) (ref₀ : Coins refresherBytes)
    (r₀ : Coins uovM) (x₁ : XR) (o1 : ByteArray × ByteArray) (s : ShP (RowH R)) : Finset (K2 pP) :=
  qf0 Hb A Qk Qr Γ ref₀ r₀ (x₁.1, h3At s (keyP Hb x₁.1.2)) o1 default s

/-- **Session `1`'s continuation, session `0` real with its slice its column.** -/
noncomputable def K1RSh (Hb : Hashes) (A : AdversaryRA (RowH R)) (ref₁ : Coins refresherBytes)
    (r₁ : Coins uovM) (x₀ : XR) (s : ShP (RowH R)) : Cont2 :=
  K1R Hb A ref₁ r₁ (x₀.1, h3At s (keyP Hb x₀.1.2)) default s

/-- **Session `1`'s read set, session `0`'s slice its column.** -/
noncomputable def qf1Sh (Hb : Hashes) (A : AdversaryRA (RowH R)) (Qk : TbP (RowH R) → RSP)
    (Qr : Bytes → Bytes → TbP (RowH R) → RSP) (Γ : Tab2G pP) (ref₁ : Coins refresherBytes)
    (r₁ : Coins uovM) (x₀ : XR) (o1 : ByteArray × ByteArray) (s : ShP (RowH R)) : Finset (K2 pP) :=
  qf1 Hb A Qk Qr Γ ref₁ r₁ (x₀.1, h3At s (keyP Hb x₀.1.2)) o1 default s

variable {i2 i5 iE : ℕ} (hk : ConsP Qk fun t : TbP (RowH R) => A.keyOf t.1 t.2)
  (hck : CardP Qk 0 i2 i5 iE)
  (hr : ∀ t₀ t₁, ConsP (Qr t₀ t₁) fun t : TbP (RowH R) => A.respOf t₀ t₁ t.1 t.2)
  (hcr : ∀ t₀ t₁, CardP (Qr t₀ t₁) 0 i2 i5 iE)
include hk hck hr hcr

/-- Session `0`'s read set reads no slice: neither its own nor session `1`'s, except session
`1`'s at its randomness (session `1`'s step 1). -/
lemma qf0_sl (ref₀ : Coins refresherBytes) (r₀ : Coins uovM)
    (x : Coins proveSeedBytes × Coins refresherBytes × Coins uovM) {G G' : Tab3} (g g' : Tab3)
    (o1 : ByteArray × ByteArray) (s : ShP (RowH R)) (h : G x.1 = G' x.1) :
    qf0 Hb A Qk Qr Γ ref₀ r₀ (x, G) o1 g s = qf0 Hb A Qk Qr Γ ref₀ r₀ (x, G') o1 g' s := by
  have eK := ConsP.free hk hck (g, G) (g', G') (Γ, s.2)
  have eK1 : Qk ((g', G'), (Γ, s.2)) = Qk ((g, G), (Γ, s.2)) := eK.1
  have eK2 : A.keyOf (g', G') (Γ, s.2) = A.keyOf (g, G) (Γ, s.2) := eK.2
  have eR : ∀ t₀ t₁, Qr t₀ t₁ ((g', G'), (Γ, s.2)) = Qr t₀ t₁ ((g, G), (Γ, s.2)) := fun t₀ t₁ =>
    (ConsP.free (hr t₀ t₁) (hcr t₀ t₁) (g, G) (g', G') (Γ, s.2)).1
  have es : s1R Hb (x, G) s = s1R Hb (x, G') s := s1R_g3 x s h
  unfold qf0 AdversaryRA.mixQ
  simp only [eK1, eK2, eR, es]

/-- Session `1`'s read set reads no slice, except session `0`'s at its randomness. -/
lemma qf1_sl (ref₁ : Coins refresherBytes) (r₁ : Coins uovM)
    (x : Coins proveSeedBytes × Coins refresherBytes × Coins uovM) {G G' : Tab3} (g g' : Tab3)
    (o1 : ByteArray × ByteArray) (s : ShP (RowH R)) (h : G x.1 = G' x.1) :
    qf1 Hb A Qk Qr Γ ref₁ r₁ (x, G) o1 g s = qf1 Hb A Qk Qr Γ ref₁ r₁ (x, G') o1 g' s := by
  have eK := ConsP.free hk hck (G, g) (G', g') (Γ, s.2)
  have eK1 : Qk ((G', g'), (Γ, s.2)) = Qk ((G, g), (Γ, s.2)) := eK.1
  have eK2 : A.keyOf (G', g') (Γ, s.2) = A.keyOf (G, g) (Γ, s.2) := eK.2
  have eR : ∀ t₀ t₁, Qr t₀ t₁ ((G', g'), (Γ, s.2)) = Qr t₀ t₁ ((G, g), (Γ, s.2)) := fun t₀ t₁ =>
    (ConsP.free (hr t₀ t₁) (hcr t₀ t₁) (G, g) (G', g') (Γ, s.2)).1
  have es : s1R Hb (x, G) s = s1R Hb (x, G') s := s1R_g3 x s h
  unfold qf1 AdversaryRA.mixQ
  simp only [eK1, eK2, eR, es]

end Conts

section K1Free

variable {Hb : Hashes} {A : AdversaryRA (RowH R)} {i5 iE : ℕ}

/-- Session `1`'s continuation (session `0` real) reads no slice, except session `0`'s at its
randomness. -/
lemma K1R_sl (hI : A.IBudget 0 i5 iE) (ref₁ : Coins refresherBytes) (r₁ : Coins uovM)
    (x : Coins proveSeedBytes × Coins refresherBytes × Coins uovM) {G G' : Tab3} (g g' : Tab3)
    (s : ShP (RowH R)) (h : G x.1 = G' x.1) :
    K1R Hb A ref₁ r₁ (x, G) g s = K1R Hb A ref₁ r₁ (x, G') g' s := by
  unfold K1R
  rw [AdversaryRA.at_free hI (G, g) (G', g')]
  simp only [tR]
  rw [s1R_g3 x s h]

end K1Free

/-! ## The collision probabilities on the shared tables -/

lemma preR2_congr {R' : Type} [CipherRow R'] {Hb : Hashes} {st : Statement} {r : ByteArray}
    {K K' : Tab3 → ShG R' st.params → Cont2} (a : (Bytes 16 × Tab3) × ShG R' st.params)
    (h : K a.1.2 a.2 = K' a.1.2 a.2) : preR2 Hb st r K a = preR2 Hb st r K' a := by
  unfold preR2
  rw [h]

section BadPr

variable {Hb : Hashes} {A : AdversaryRA (RowH R)} {Qk : TbP (RowH R) → RSP}
  {Qr : Bytes → Bytes → TbP (RowH R) → RSP}

/-- **The collision error of one session with one shared `H₃`**:
`2⁻¹¹³ + εz(6i_E + 13824, 6i₅ + 2184, 6i_E + 18431) + 2i₂·2⁻¹²⁸`. -/
noncomputable def εcolSh (R : Type) [Fintype R] [CipherRow R] [ZKRow R] (i2 i5 iE : ℕ) : ℝ :=
  1 / 2 ^ 113 + ZKRow.εz R pP (6 * iE + 13824) (6 * i5 + 2184) (6 * iE + 18431) +
    (i2 + i2 : ℕ) / 2 ^ 128

variable {i2 i5 iE : ℕ} (hHb : HashesWF Hb) (hk : ConsP Qk fun t : TbP (RowH R) => A.keyOf t.1 t.2)
  (hck : CardP Qk 0 i2 i5 iE)
  (hr : ∀ t₀ t₁, ConsP (Qr t₀ t₁) fun t : TbP (RowH R) => A.respOf t₀ t₁ t.1 t.2)
  (hcr : ∀ t₀ t₁, CardP (Qr t₀ t₁) 0 i2 i5 iE)
include hHb hk hck hr hcr

/-- **Session `0`'s collision probability, one shared `H₃`.** -/
theorem pr_bad0HSh [ZKRow R] [ZK2ARow R] :
    pr ((CH (RowH R) × Tab2G pP) × Tab2G pP) (fun w =>
      bad0H Hb A Qk Qr (τC Hb w.1.1) w.1.2 w.2) ≤ εcolSh R i2 i5 iE := by
  rw [← pr_equiv eqB0]
  refine pr_le_of_fst fun ζ => ?_
  obtain ⟨Γ, ⟨ref₀, r₀⟩, x₁⟩ := ζ
  have hI := AdversaryRA.IBudget.subst hk hck hr hcr Γ
  have hh := fun G : Tab3 => hyp2RA_R hHb hI ref₀ r₀ (x₁.1, G)
  have h := pr_tail2Sh Hb (stOf ref₀) (toBA (List.ofFn r₀)) uovM (keyP Hb (ref₀, r₀))
    (K0sA Hb (A.subst Qk Qr Γ) ref₀ r₀ x₁) (fun s => (hh _).hyp default s) (hh default).size
    (fun s G2 => K0_h23 hI ref₀ r₀ (x₁.1, h3At s (keyP Hb x₁.1.2)) default s G2)
    (fun o1 => rd5_h3At (f := fun G s => K0 Hb (A.subst Qk Qr Γ) ref₀ r₀ (x₁.1, G) default s o1)
      (fun G => (hh G).h5 o1 default) (keyP Hb x₁.1.2))
    (fun o1 => rdE_h3At (f := fun G s => K0 Hb (A.subst Qk Qr Γ) ref₀ r₀ (x₁.1, G) default s o1)
      x₁.1.1 (fun G G' s h => by rw [K0_g3 hI ref₀ r₀ x₁.1 default s h])
      (fun G => (hh G).hE o1 default) (keyP Hb x₁.1.2))
    hHb (smallParams_of_le (p := pP) (by decide) (by decide))
    (qf0Sh Hb A Qk Qr Γ ref₀ r₀ x₁)
    (fun o1 s G2 => qf0_h2 Hb Γ ref₀ r₀ (x₁.1, h3At s (keyP Hb x₁.1.2)) o1 default s G2)
    (fun o1 s => mixQ_card Γ hk hck hr hcr _ _ _ _)
    (fun o1 => rd5_h3At (f := fun G s => qf0 Hb A Qk Qr Γ ref₀ r₀ (x₁.1, G) o1 default s)
      (fun G => qf0_rd5 Hb Γ hk hck hr hcr ref₀ r₀ (x₁.1, G) o1 default) (keyP Hb x₁.1.2))
    (fun o1 => rdE_h3At (f := fun G s => qf0 Hb A Qk Qr Γ ref₀ r₀ (x₁.1, G) o1 default s)
      x₁.1.1 (fun G G' s h => qf0_sl Γ hk hck hr hcr ref₀ r₀ x₁.1 default default o1 s h)
      (fun G => qf0_rdE Hb Γ hk hck hr hcr hHb ref₀ r₀ (x₁.1, G) o1 default) (keyP Hb x₁.1.2))
  refine le_trans (pr_mono fun a hb => ?_) (h.trans ?_)
  · obtain ⟨⟨ρ, g⟩, G2, s₂⟩ := a
    have hb' := bad0_event hHb ref₀ r₀ (x₁.1, h3At (G2, s₂) (keyP Hb x₁.1.2)) Γ ρ
      (h3At (G2, s₂) (keyP Hb (ref₀, r₀))) G2 s₂ hb
    obtain ⟨hk1, κ, hκ, hblk⟩ := hb'
    have eK := K0_free (Hb := Hb) hI ref₀ r₀ (x₁.1, h3At (G2, s₂) (keyP Hb x₁.1.2))
      (h3At (G2, s₂) (keyP Hb (ref₀, r₀))) default (G2, s₂)
    refine ⟨?_, κ, ?_, ?_⟩
    · show (K0 Hb (A.subst Qk Qr Γ) ref₀ r₀ (x₁.1, h3At (G2, s₂) (keyP Hb x₁.1.2)) default (G2, s₂)
        _).isSome
      rw [← eK]
      exact hk1
    · show κ ∈ qf0 Hb A Qk Qr Γ ref₀ r₀ (x₁.1, h3At (G2, s₂) (keyP Hb x₁.1.2)) _ default (G2, s₂)
      rw [← qf0_sl Γ hk hck hr hcr ref₀ r₀ x₁.1 (h3At (G2, s₂) (keyP Hb (ref₀, r₀))) default _ _ rfl]
      exact hκ
    · refine hblk.trans ?_
      exact congrArg (blk (preLen pP)) <| preR2_congr (Hb := Hb) (st := stOf ref₀) (r := toBA (List.ofFn r₀)) (K := K0 Hb (A.subst Qk Qr Γ) ref₀ r₀ (x₁.1, h3At (G2, s₂) (keyP Hb x₁.1.2)))
        (K' := fun _ => K0sA Hb (A.subst Qk Qr Γ) ref₀ r₀ x₁)
        ((ρ, h3At (G2, s₂) (keyP Hb (ref₀, r₀))), (G2, s₂)) eK
  · have m := ZKRow.εz_mono (R := R) pP
      (q3 := iE + 4607 + iE + 1 + (iE + 4607 + iE + 1) + (iE + 4607 + iE + 1))
      (q3' := 6 * iE + 13824)
      (q5 := i5 + 624 + i5 + (i5 + 624 + i5) + 312 + (i5 + 624 + i5)) (q5' := 6 * i5 + 2184)
      (qE := iE + 4607 + iE + 1 + (iE + 4607 + iE + 1) + 4607 + (iE + 4607 + iE + 1))
      (qE' := 6 * iE + 18431) (by omega) (by omega) (by omega)
    unfold εcolSh
    show 1 / 2 ^ 113 + ZKRow.εz R pP _ _ _ + ((i2 + i2 : ℕ) : ℝ) / 2 ^ 128 ≤ _
    linarith

/-- **Session `1`'s collision probability, one shared `H₃`.** -/
theorem pr_bad1HSh [ZKRow R] [ZK2ARow R] :
    pr ((CH (RowH R) × Tab2G pP) × Tab2G pP) (fun w =>
      bad1H Hb A Qk Qr (τC Hb w.1.1) w.1.2 w.2) ≤ εcolSh R i2 i5 iE := by
  rw [← pr_equiv eqB1]
  refine pr_le_of_fst fun ζ => ?_
  obtain ⟨Γ, x₀, ref₁, r₁⟩ := ζ
  have hI := AdversaryRA.IBudget.subst hk hck hr hcr Γ
  have hh := fun G : Tab3 => hyp2RA_R1 Hb hHb hI ref₁ r₁ (x₀.1, G)
  have h := pr_tail2Sh Hb (stOf ref₁) (toBA (List.ofFn r₁)) uovM (keyP Hb (ref₁, r₁))
    (K1RSh Hb (A.subst Qk Qr Γ) ref₁ r₁ x₀) (fun s => (hh _).hyp default s) (hh default).size
    (fun s G2 => K1R_h23 Hb hI ref₁ r₁ (x₀.1, h3At s (keyP Hb x₀.1.2)) default s G2)
    (fun o1 => rd5_h3At (f := fun G s => K1R Hb (A.subst Qk Qr Γ) ref₁ r₁ (x₀.1, G) default s o1)
      (fun G => (hh G).h5 o1 default) (keyP Hb x₀.1.2))
    (fun o1 => rdE_h3At (f := fun G s => K1R Hb (A.subst Qk Qr Γ) ref₁ r₁ (x₀.1, G) default s o1)
      x₀.1.1 (fun G G' s h => by rw [K1R_sl hI ref₁ r₁ x₀.1 default default s h])
      (fun G => (hh G).hE o1 default) (keyP Hb x₀.1.2))
    hHb (smallParams_of_le (p := pP) (by decide) (by decide))
    (qf1Sh Hb A Qk Qr Γ ref₁ r₁ x₀)
    (fun o1 s G2 => qf1_h2 Hb Γ ref₁ r₁ (x₀.1, h3At s (keyP Hb x₀.1.2)) o1 default s G2)
    (fun o1 s => mixQ_card Γ hk hck hr hcr _ _ _ _)
    (fun o1 => rd5_h3At (f := fun G s => qf1 Hb A Qk Qr Γ ref₁ r₁ (x₀.1, G) o1 default s)
      (fun G => qf1_rd5 Hb Γ hk hck hr hcr ref₁ r₁ (x₀.1, G) o1 default) (keyP Hb x₀.1.2))
    (fun o1 => rdE_h3At (f := fun G s => qf1 Hb A Qk Qr Γ ref₁ r₁ (x₀.1, G) o1 default s)
      x₀.1.1 (fun G G' s h => qf1_sl Γ hk hck hr hcr ref₁ r₁ x₀.1 default default o1 s h)
      (fun G => qf1_rdE Hb Γ hk hck hr hcr hHb ref₁ r₁ (x₀.1, G) o1 default) (keyP Hb x₀.1.2))
  refine le_trans (pr_mono fun a hb => ?_) (h.trans ?_)
  · obtain ⟨⟨ρ, g⟩, G2, s₂⟩ := a
    have hb' := bad1_event hHb ref₁ r₁ (x₀.1, h3At (G2, s₂) (keyP Hb x₀.1.2)) Γ ρ
      (h3At (G2, s₂) (keyP Hb (ref₁, r₁))) G2 s₂ hb
    obtain ⟨hk1, κ, hκ, hblk⟩ := hb'
    have eK := K1R_sl (Hb := Hb) hI ref₁ r₁ x₀.1 (G := h3At (G2, s₂) (keyP Hb x₀.1.2))
      (G' := h3At (G2, s₂) (keyP Hb x₀.1.2)) (h3At (G2, s₂) (keyP Hb (ref₁, r₁))) default (G2, s₂) rfl
    refine ⟨?_, κ, ?_, ?_⟩
    · show (K1R Hb (A.subst Qk Qr Γ) ref₁ r₁ (x₀.1, h3At (G2, s₂) (keyP Hb x₀.1.2)) default (G2, s₂)
        _).isSome
      rw [← eK]
      exact hk1
    · show κ ∈ qf1 Hb A Qk Qr Γ ref₁ r₁ (x₀.1, h3At (G2, s₂) (keyP Hb x₀.1.2)) _ default (G2, s₂)
      rw [← qf1_sl Γ hk hck hr hcr ref₁ r₁ x₀.1 (h3At (G2, s₂) (keyP Hb (ref₁, r₁))) default _ _ rfl]
      exact hκ
    · refine hblk.trans ?_
      exact congrArg (blk (preLen pP)) <| preR2_congr (Hb := Hb) (st := stOf ref₁) (r := toBA (List.ofFn r₁)) (K := K1R Hb (A.subst Qk Qr Γ) ref₁ r₁ (x₀.1, h3At (G2, s₂) (keyP Hb x₀.1.2)))
        (K' := fun _ => K1RSh Hb (A.subst Qk Qr Γ) ref₁ r₁ x₀)
        ((ρ, h3At (G2, s₂) (keyP Hb (ref₁, r₁))), (G2, s₂)) eK
  · have m := ZKRow.εz_mono (R := R) pP
      (q3 := iE + 4607 + iE + 1 + (iE + 4607 + iE + 1) + (iE + 4607 + iE + 1))
      (q3' := 6 * iE + 13824)
      (q5 := i5 + 624 + i5 + (i5 + 624 + i5) + 312 + (i5 + 624 + i5)) (q5' := 6 * i5 + 2184)
      (qE := iE + 4607 + iE + 1 + (iE + 4607 + iE + 1) + 4607 + (iE + 4607 + iE + 1))
      (qE' := 6 * iE + 18431) (by omega) (by omega) (by omega)
    unfold εcolSh
    show 1 / 2 ^ 113 + ZKRow.εz R pP _ _ _ + ((i2 + i2 : ℕ) : ℝ) / 2 ^ 128 ≤ _
    linarith

end BadPr

/-! ## One world -/

section World

variable {Hb : Hashes} {A : AdversaryRA (RowH R)} {Qk : TbP (RowH R) → RSP}
  {Qr : Bytes → Bytes → TbP (RowH R) → RSP}

/-- **The collision term of one world, one shared `H₃`.** -/
noncomputable def h23WSh (R : Type) [Fintype R] [CipherRow R] [ZKRow R] (i2 i5 iE : ℕ) : ℝ :=
  if i2 = 0 then 0 else 2 * εcolSh R i2 i5 iE

variable {i2 i5 iE : ℕ} (hHb : HashesWF Hb) (hk : ConsP Qk fun t : TbP (RowH R) => A.keyOf t.1 t.2)
  (hck : CardP Qk 0 i2 i5 iE)
  (hr : ∀ t₀ t₁, ConsP (Qr t₀ t₁) fun t : TbP (RowH R) => A.respOf t₀ t₁ t.1 t.2)
  (hcr : ∀ t₀ t₁, CardP (Qr t₀ t₁) 0 i2 i5 iE)
include hHb hk hck hr hcr

/-- **World `false` with one shared `H₃`, the interaction's `H₂³` reads taken out.** -/
theorem G0RASh_subst_close [ZKRow R] [ZK2ARow R] :
    |pr ((XR × XR) × ShP (RowH R)) (fun z => G0RA Hb A (τR Hb z)) -
        pr (Tab2G pP × ((XR × XR) × ShP (RowH R)))
          (fun w => G0RA Hb (A.subst Qk Qr w.1) (τR Hb w.2))| ≤
      h23WSh R i2 i5 iE := by
  have hagree : ∀ v : (CH (RowH R) × Tab2G pP) × Tab2G pP,
      ¬ badH Hb A Qk Qr (τC Hb v.1.1) v.1.2 v.2 →
      (GF Hb A (τC Hb v.1.1) (intH Hb A (τC Hb v.1.1) v.1.2)
          (patchT (readH Hb A Qk Qr (τC Hb v.1.1) v.1.2) v.1.2 v.2) ↔
        G0RA Hb (A.subst Qk Qr v.1.2) (zH (τC Hb v.1.1) v.2)) := fun v hv =>
    (GF_iff_at Hb (τC Hb v.1.1) v.1.2 _).trans (G0_at_iff_subst Hb (τC Hb v.1.1) v.1.2 v.2 hv)
  have hab := abs_pr_sub_le_of_agree
    (fun v : (CH (RowH R) × Tab2G pP) × Tab2G pP =>
      GF Hb A (τC Hb v.1.1) (intH Hb A (τC Hb v.1.1) v.1.2)
        (patchT (readH Hb A Qk Qr (τC Hb v.1.1) v.1.2) v.1.2 v.2))
    (fun v => G0RA Hb (A.subst Qk Qr v.1.2) (zH (τC Hb v.1.1) v.2))
    (fun v => badH Hb A Qk Qr (τC Hb v.1.1) v.1.2 v.2) hagree
  have e2 : pr (Tab2G pP × ((XR × XR) × ShP (RowH R)))
        (fun w => G0RA Hb (A.subst Qk Qr w.1) (τR Hb w.2)) =
      pr ((CH (RowH R) × Tab2G pP) × Tab2G pP)
        (fun v => G0RA Hb (A.subst Qk Qr v.1.2) (zH (τC Hb v.1.1) v.2)) :=
    (pr_equiv eqW (fun w => G0RA Hb (A.subst Qk Qr w.1) (τR Hb w.2))).symm
  rw [pr_G0RASh_resample Hb hk hr, e2]
  refine hab.trans ?_
  unfold h23WSh
  split_ifs with h0
  · refine le_of_eq ((pr_congr fun v => iff_false_intro fun hb => ?_).trans pr_false)
    have hc : readH Hb A Qk Qr (τC Hb v.1.1) v.1.2 = ∅ := by
      have := mixQ_card v.1.2 hk hck hr hcr (tqH Hb A (τC Hb v.1.1) v.1.2).1
        (tqH Hb A (τC Hb v.1.1) v.1.2).2 (slH (τC Hb v.1.1)) v.1.1.2
      rw [h0] at this
      exact Finset.card_eq_zero.1 (Nat.le_zero.1 this)
    have hp : patchT (readH Hb A Qk Qr (τC Hb v.1.1) v.1.2) v.1.2 v.2 = v.2 := by
      rw [hc]; funext κ; exact patchT_of_not_mem _ _ (Finset.notMem_empty κ)
    rcases (badH_iff Hb A Qk Qr _ _ _).1 hb with h | h
    · exact h (by rw [hp])
    · exact h (by rw [hp])
  · rw [pr_congr fun v : (CH (RowH R) × Tab2G pP) × Tab2G pP =>
      badH_iff Hb A Qk Qr (τC Hb v.1.1) v.1.2 v.2]
    have h0' := pr_bad0HSh hHb hk hck hr hcr
    have h1' := pr_bad1HSh hHb hk hck hr hcr
    have := pr_or_le (fun v : (CH (RowH R) × Tab2G pP) × Tab2G pP =>
        bad0H Hb A Qk Qr (τC Hb v.1.1) v.1.2 v.2)
      (fun v => bad1H Hb A Qk Qr (τC Hb v.1.1) v.1.2 v.2)
    linarith

end World

/-! ## Blindness -/

section Blind

/-- **The collision term of the bound, one shared `H₃`**: `0` if the interaction does not read
`H₂³`, else `4·(2⁻¹¹³ + εz(pP; 6i_E + 13824, 6i₅ + 2184, 6i_E + 18431) + 2i₂·2⁻¹²⁸)`. -/
noncomputable def h23HSh (R : Type) [Fintype R] [CipherRow R] [ZKRow R] (i2 i5 iE : ℕ) : ℝ :=
  if i2 = 0 then 0 else 4 * εcolSh R i2 i5 iE

lemma two_h23WSh [ZKRow R] (i2 i5 iE : ℕ) :
    h23WSh R i2 i5 iE + h23WSh R i2 i5 iE = h23HSh R i2 i5 iE := by
  unfold h23WSh h23HSh
  split_ifs <;> ring

/-- **PomFRIT blindness with one shared `H₃` and an Issuer whose interaction reads every table,
`H₂³` included** (ROM and ideal cipher, label rows, the Lean prover on the shared tables, SHAKE as
the base record, every type of cipher rows): the guess reads the rows (cipher and `H₃`) at `q_E`
keys, `H₅` at `q₅`, `H₂³` freely, no slot slice; the key stage and the response stage read, jointly,
no slot slice, `i₂` `H₂³` keys, `i₅` `H₅` keys and `i_E` rows (`IBudgetH 0 i₂ i₅ i_E`):

    |Pr[W₀] − Pr[W₁]| ≤ 4·εz(pP; q_E + 6i_E + 23035, q₅ + 6i₅ + 1872, q_E + 6i_E + 23035)
                         + 2·noHitProb + 2·2⁻¹²⁸ + h23HSh(i₂, i₅, i_E). -/
theorem blindnessRAHSh_numG [ZKRow R] [ZK2ARow R] (A : AdversaryRA (RowH R)) {q5 qE i2 i5 iE : ℕ}
    (hA : A.GBudget 0 q5 qE) (hI : A.IBudgetH 0 i2 i5 iE) :
    |pr ((XR × XR) × ShP (RowH R)) (realGameRASh Hashes.shake A false) -
        pr ((XR × XR) × ShP (RowH R)) (realGameRASh Hashes.shake A true)| ≤
      4 * ZKRow.εz R pP (qE + 6 * iE + 23035) (q5 + 6 * i5 + 1872) (qE + 6 * iE + 23035) +
        2 * noHitProb + 2 / 2 ^ 128 + h23HSh R i2 i5 iE := by
  obtain ⟨Qk, hk, hck⟩ := hI.k
  choose Qr hr hcr using hI.r
  have hk' : ConsP Qk fun t : TbP (RowH R) => A.keyOf t.1 t.2 := hk
  have hck' : CardP Qk 0 i2 i5 iE := hck
  have hr' : ∀ t₀ t₁, ConsP (Qr t₀ t₁) fun t : TbP (RowH R) => A.respOf t₀ t₁ t.1 t.2 := hr
  have hcr' : ∀ t₀ t₁, CardP (Qr t₀ t₁) 0 i2 i5 iE := hcr
  have hF := AdversaryRA.at_freeH hI
  have h0 : pr ((XR × XR) × ShP (RowH R)) (realGameRASh Hashes.shake A false) =
      pr ((XR × XR) × ShP (RowH R)) (fun z => G0RA Hashes.shake A (τR Hashes.shake z)) :=
    pr_congr fun z => (realGameRASh_iff' Hashes.shake hA hF false z).trans (realGameRA_iff _ _ _)
  have h1 := pr_realGameRASh_true Hashes.shake hA hF
  -- World `false` and world `true` (the exchanged Issuer, the exchanged read sets).
  have cA := G0RASh_subst_close hashesWF_shake hk' hck' hr' hcr'
  have cS := G0RASh_subst_close (A := A.swap) hashesWF_shake (AdversaryRA.consP_swapK hk')
    (AdversaryRA.cardP_swap hck') (AdversaryRA.consP_swapR hr')
    (fun t₀ t₁ => AdversaryRA.cardP_swap (hcr' t₁ t₀))
  -- The substituted Issuers satisfy the hypotheses of `blindnessRASh_numG`.
  have hmid : |pr (Tab2G pP × ((XR × XR) × ShP (RowH R)))
        (fun w => G0RA Hashes.shake (A.subst Qk Qr w.1) (τR Hashes.shake w.2)) -
      pr (Tab2G pP × ((XR × XR) × ShP (RowH R)))
        (fun w => G0RA Hashes.shake ((A.subst Qk Qr w.1).swap) (τR Hashes.shake w.2))| ≤
      4 * ZKRow.εz R pP (qE + 6 * iE + 23035) (q5 + 6 * i5 + 1872) (qE + 6 * iE + 23035) +
        2 * noHitProb + 2 / 2 ^ 128 := by
    refine abs_pr_prod_sub_le _ _ fun Γ => ?_
    have hB : (A.subst Qk Qr Γ).GBudget 0 (i5 + i5 + q5) (iE + iE + qE) :=
      AdversaryRA.GBudget.subst hA hk' hck' hr' hcr' Γ
    have hBI := AdversaryRA.IBudget.subst hk' hck' hr' hcr' Γ
    have hb := blindnessRASh_numG (A.subst Qk Qr Γ) hB hBI
    rw [pr_congr fun z => (realGameRASh_iff hB hBI false z).trans (realGameRA_iff _ _ _),
      pr_realGameRASh_true Hashes.shake hB (AdversaryRA.at_free hBI)] at hb
    have m := ZKRow.εz_mono (R := R) pP
      (q3 := iE + iE + qE + 4 * iE + 23035) (q3' := qE + 6 * iE + 23035)
      (q5 := i5 + i5 + q5 + 4 * i5 + 1872) (q5' := q5 + 6 * i5 + 1872)
      (qE := iE + iE + qE + 4 * iE + 23035) (qE' := qE + 6 * iE + 23035)
      (by omega) (by omega) (by omega)
    exact hb.trans (by linarith)
  have e : pr (Tab2G pP × ((XR × XR) × ShP (RowH R)))
        (fun w => G0RA Hashes.shake ((A.subst Qk Qr w.1).swap) (τR Hashes.shake w.2)) =
      pr (Tab2G pP × ((XR × XR) × ShP (RowH R)))
        (fun w => G0RA Hashes.shake (A.swap.subst
          (fun t => AdversaryRA.swapRS (Qk ((t.1.2, t.1.1), t.2)))
          (fun t₀ t₁ t => AdversaryRA.swapRS (Qr t₁ t₀ ((t.1.2, t.1.1), t.2))) w.1)
          (τR Hashes.shake w.2)) := by
    simp only [AdversaryRA.swap_subst]
  rw [e] at hmid
  rw [h0, h1, ← two_h23WSh]
  have t1 := abs_sub_le
    (pr ((XR × XR) × ShP (RowH R)) (fun z => G0RA Hashes.shake A (τR Hashes.shake z)))
    (pr (Tab2G pP × ((XR × XR) × ShP (RowH R)))
      (fun w => G0RA Hashes.shake (A.subst Qk Qr w.1) (τR Hashes.shake w.2)))
    (pr ((XR × XR) × ShP (RowH R)) (fun z => G0RA Hashes.shake A.swap (τR Hashes.shake z)))
  have t2 := abs_sub_le
    (pr (Tab2G pP × ((XR × XR) × ShP (RowH R)))
      (fun w => G0RA Hashes.shake (A.subst Qk Qr w.1) (τR Hashes.shake w.2)))
    (pr (Tab2G pP × ((XR × XR) × ShP (RowH R)))
      (fun w => G0RA Hashes.shake (A.swap.subst
        (fun t => AdversaryRA.swapRS (Qk ((t.1.2, t.1.1), t.2)))
        (fun t₀ t₁ t => AdversaryRA.swapRS (Qr t₁ t₀ ((t.1.2, t.1.1), t.2))) w.1)
        (τR Hashes.shake w.2)))
    (pr ((XR × XR) × ShP (RowH R)) (fun z => G0RA Hashes.shake A.swap (τR Hashes.shake z)))
  rw [abs_sub_comm (pr _ (fun z => G0RA Hashes.shake A.swap (τR Hashes.shake z)))] at cS
  linarith

/-- **PomFRIT blindness with one shared `H₃` and an Issuer whose interaction reads every table,
`H₂³` included** (function rows, every term explicit):

    |Pr[W₀] − Pr[W₁]| ≤ 4·εRO(q_E + 6i_E + 23035, q₅ + 6i₅ + 1872, q_E + 6i_E + 23035)
                         + 2·noHitProb + 2·2⁻¹²⁸
                         + [i₂ > 0]·4·(2⁻¹¹³ + εRO(6i_E + 13824, 6i₅ + 2184, 6i_E + 18431)
                                        + 2i₂·2⁻¹²⁸). -/
theorem blindnessRAHSh_num (A : AdversaryRA (RowH (Blk → Blk))) {q5 qE i2 i5 iE : ℕ}
    (hA : A.GBudget 0 q5 qE) (hI : A.IBudgetH 0 i2 i5 iE) :
    |pr ((XR × XR) × ShP (RowH (Blk → Blk))) (realGameRASh Hashes.shake A false) -
        pr ((XR × XR) × ShP (RowH (Blk → Blk))) (realGameRASh Hashes.shake A true)| ≤
      4 * εRO (qE + 6 * iE + 23035) (q5 + 6 * i5 + 1872) (qE + 6 * iE + 23035) +
        2 * noHitProb + 2 / 2 ^ 128 +
        (if i2 = 0 then 0 else
          4 * (1 / 2 ^ 113 + εRO (6 * iE + 13824) (6 * i5 + 2184) (6 * iE + 18431) +
            (i2 + i2 : ℕ) / 2 ^ 128)) :=
  blindnessRAHSh_numG A hA hI

/-- **`blindnessRAHSh_num` with AES as uniformly random permutations.** -/
theorem blindnessRAHSh_num_perm (A : AdversaryRA (RowH (Equiv.Perm Blk))) {q5 qE i2 i5 iE : ℕ}
    (hA : A.GBudget 0 q5 qE) (hI : A.IBudgetH 0 i2 i5 iE) :
    |pr ((XR × XR) × ShP (RowH (Equiv.Perm Blk))) (realGameRASh Hashes.shake A false) -
        pr ((XR × XR) × ShP (RowH (Equiv.Perm Blk))) (realGameRASh Hashes.shake A true)| ≤
      4 * εROPm pP (qE + 6 * iE + 23035) (q5 + 6 * i5 + 1872) (qE + 6 * iE + 23035) +
        2 * noHitProb + 2 / 2 ^ 128 +
        (if i2 = 0 then 0 else
          4 * (1 / 2 ^ 113 + εROPm pP (6 * iE + 13824) (6 * i5 + 2184) (6 * iE + 18431) +
            (i2 + i2 : ℕ) / 2 ^ 128)) :=
  blindnessRAHSh_numG A hA hI

end Blind

end VoleMole.Privacy.PomFRIT
