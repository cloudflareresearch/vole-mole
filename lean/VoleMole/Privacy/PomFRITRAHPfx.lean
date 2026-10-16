import VoleMole.Privacy.PomFRITRAH
import VoleMole.Privacy.PermRA

/-!
# PomFRIT blindness with an `H₂³`-reading Issuer: the collision term counts prefixes

`blindnessRAH_lean_num` (`Privacy/PomFRITRAH.lean`) charges the collision term (a real session's
grinding block meets the interaction's `H₂³` reads) `2⁻¹²⁸` per `H₂³` **key** the interaction
reads (`2i₂·2⁻¹²⁸` per session and world). But a session's grinding block is all `2³²` keys
`(pre, ctr)` of one prefix `pre`, and the event is that some read key has the session's prefix:
`pr_simEv2` already bounds it by the number of distinct **tails** of the read prefixes. So the
charge is per prefix, not per key, and an interaction that reads whole blocks (another honest
session reads the `2³²` grinding points of its own prefix) pays `2⁻¹²⁸` per block, not `2⁻⁹⁶`.

* `ZK.Sim.pr_tail2A_pfx`: `pr_tail2A` with the bound `m` on the number of distinct prefixes
  `(Qf o1 g s).image Prod.fst` of the read set in place of its size. The read set is replaced by
  one representative key per prefix (`blkRep`), which has the same prefixes and at most `m` keys
  and is read off the same tables, and `pr_tail2A` is applied to it.
* `IBudgetHB i₃ b₂ i₅ i_E`: `IBudgetH` with the `H₂³` read sets bounded by their number of
  prefixes (`b₂`) instead of their size (`IBudgetH.toB`: `IBudgetH i₃ i₂ i₅ i_E` implies
  `IBudgetHB i₃ i₂ i₅ i_E`). Nothing else in the proof uses the number of `H₂³` keys: the lazy
  sampling of `H₂³` needs no bound, and the existing lemmas, which take one, are applied with the
  size of the whole table (`CardPB.cardP`).
* `pr_bad0H_pfx`, `pr_bad1H_pfx`: the sessions' collision terms, `≤ εcol R i₃ b₂ i₅ i_E`
  (`2⁻¹¹³ + εz(6i₃, 6i₅ + 2184, 6i_E + 18428) + 2b₂·2⁻¹²⁸`).
* **`blindnessRAH_lean_numG_pfx`**, **`blindnessRAH_lean_num_pfx`**,
  **`blindnessRAH_lean_num_perm_pfx`**: the bounds of `blindnessRAH_lean_numG`, `_num`, `_num_perm`
  with `b₂` (prefixes) in place of `i₂` (keys) in the collision term:

      |Pr[W₀] − Pr[W₁]| ≤ 4·εz(pP; q₃ + 6i₃, q₅ + 6i₅ + 1872, q_E + 6i_E + 23035)
                           + 2·noHitProb + 2·2⁻¹²⁸ + h23H(i₃, b₂, i₅, i_E).

  Since `IBudgetH i₃ i₂ i₅ i_E` gives `IBudgetHB i₃ i₂ i₅ i_E`, this is never worse than the
  key count.
-/

open Finset

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

/-! ## The tail bound, counting prefixes -/

namespace VoleMole.ZK.Sim

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.Arith VoleMole.ZK VoleMole.Privacy

lemma nGrind_pos : 0 < nGrind := by unfold nGrind; norm_num

/-- **One representative key per prefix** of a set of `H₂³` keys (counter `0`). -/
def blkRep {p : Params} (Q : Finset (K2 p)) : Finset (K2 p) :=
  (Q.image Prod.fst).image fun b => (b, ⟨0, nGrind_pos⟩)

lemma blkRep_card_le {p : Params} (Q : Finset (K2 p)) : (blkRep Q).card ≤ (Q.image Prod.fst).card :=
  card_image_le

lemma mem_blkRep {p : Params} {Q : Finset (K2 p)} {κ : K2 p} (h : κ ∈ Q) :
    ((κ.1, ⟨0, nGrind_pos⟩) : K2 p) ∈ blkRep Q :=
  mem_image.2 ⟨κ.1, mem_image.2 ⟨κ, h, rfl⟩, rfl⟩

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R]

/-- **`pr_tail2A` counting prefixes**: the read set `Qf` has at most `m` distinct prefixes
(`(Qf o1 g s).image Prod.fst`), however many keys:

    Pr[K continues ∧ Qf meets the real prefix's block]
      ≤ 2⁻¹¹³ + εz(k₃ + a₃ + k₃, k₅ + a₅ + 312 + k₅, k_E + a_E + 4607 + k_E) + m·2^(−8·16(d−1)).

The event depends on `Qf` only through its prefixes, so `pr_tail2A` applies to `blkRep ∘ Qf`, one
key per prefix, which is read off the same tables. -/
theorem pr_tail2A_pfx [ZKRow R] [ZK2ARow R] (Hb : Hashes) (st : Statement) (r : ByteArray) (n : ℕ)
    (K : Tab3 → ShG R st.params → Cont2) {k3 k5 kE : ℕ} (hh : Hyp2RA st r n K k3 k5 kE)
    (hHb : HashesWF Hb) (hp : SmallParams st.params)
    (Qf : ByteArray × ByteArray → Tab3 → ShG R st.params → Finset (K2 st.params))
    (hQ2 : ∀ o1 g (s : ShG R st.params) (G2 : Tab2G st.params), Qf o1 g (G2, s.2) = Qf o1 g s)
    {m : ℕ} (hm : ∀ o1 g s, ((Qf o1 g s).image Prod.fst).card ≤ m) {a3 a5 aE : ℕ}
    (hQ3 : ∀ o1 s, Rd3 (fun g => Qf o1 g s) a3) (hQ5 : ∀ o1 g, Rd5 (fun s => Qf o1 g s) a5)
    (hQE : ∀ o1 g, RdE (fun s => Qf o1 g s) aE) :
    pr ((Bytes 16 × Tab3) × ShG R st.params) (fun a =>
        (K a.1.2 a.2 (o1R2 Hb st r a)).isSome ∧
          ∃ κ ∈ Qf (o1R2 Hb st r a) a.1.2 a.2, κ.1 = blk (preLen st.params) (preR2 Hb st r K a)) ≤
      1 / 2 ^ 113 + ZKRow.εz R st.params (k3 + a3 + k3) (k5 + a5 + 312 + k5) (kE + aE + 4607 + kE) +
        m / 2 ^ (8 * (16 * (st.params.qsDegree - 1))) := by
  have h := pr_tail2A Hb st r n K hh hHb hp (fun o1 g s => blkRep (Qf o1 g s))
    (fun o1 g s G2 => by simp only [hQ2]) (fun o1 g s => (blkRep_card_le _).trans (hm o1 g s))
    (fun o1 s => (hQ3 o1 s).map blkRep) (fun o1 g => (hQ5 o1 g).map blkRep)
    (fun o1 g => (hQE o1 g).map blkRep)
  refine le_trans (pr_mono fun a ha => ?_) h
  obtain ⟨hk, κ, hκ, hb⟩ := ha
  exact ⟨hk, _, mem_blkRep hκ, hb⟩

end VoleMole.ZK.Sim

/-! ## The prefix budget and the bound -/

namespace VoleMole.Privacy.PomFRIT

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.ZK.Sim VoleMole.Arith
open VoleMole.Spec VoleMole.Spec.PomFRIT VoleMole.ZK.IC

attribute [local irreducible] commitRefresher UOVKey.eval

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R]

section Budget

/-- **The bounds of explicit read sets, `H₂³` by prefixes**: at most `a₃` keys of each slice, `H₂³`
keys of at most `b₂` prefixes, `a₅` `H₅` keys, `a_E` cipher keys. -/
def CardPB (Q : TbP R → RSP) (a3 b2 a5 aE : ℕ) : Prop :=
  ∀ t, (Q t).1.1.card ≤ a3 ∧ (Q t).1.2.card ≤ a3 ∧ ((Q t).2.1.image Prod.fst).card ≤ b2 ∧
    (Q t).2.2.1.card ≤ a5 ∧ (Q t).2.2.2.card ≤ aE

/-- **A consistent joint reader whose `H₂³` reads have at most `b₂` prefixes.** -/
def SReadsPB {X : Type*} (f : TbP R → X) (a3 b2 a5 aE : ℕ) : Prop :=
  ∃ Q : TbP R → RSP, ConsP Q f ∧ CardPB Q a3 b2 a5 aE

variable {Q : TbP R → RSP} {a3 a2 b2 a5 aE : ℕ}

/-- Any read set of `H₂³` has at most as many keys as the table. -/
lemma CardPB.cardP (h : CardPB Q a3 b2 a5 aE) : CardP Q a3 (Fintype.card (K2 pP)) a5 aE :=
  fun t => by
    obtain ⟨c1, c2, -, c4, c5⟩ := h t
    exact ⟨c1, c2, card_le_univ _, c4, c5⟩

/-- A read set has at most as many prefixes as keys. -/
lemma CardP.cardPB (h : CardP Q a3 a2 a5 aE) : CardPB Q a3 a2 a5 aE := fun t => by
  obtain ⟨c1, c2, c3, c4, c5⟩ := h t
  exact ⟨c1, c2, card_image_le.trans c3, c4, c5⟩

lemma cardPB_swap (h : CardPB Q a3 b2 a5 aE) :
    CardPB (fun t => AdversaryRA.swapRS (Q ((t.1.2, t.1.1), t.2))) a3 b2 a5 aE := fun t => by
  obtain ⟨c1, c2, c3, c4, c5⟩ := h ((t.1.2, t.1.1), t.2)
  exact ⟨c2, c1, c3, c4, c5⟩

/-- **The interaction's joint budget, `H₂³` by prefixes**: as `IBudgetH`, with the `H₂³` read sets
of the key stage and of the response stage at every pair of requests each of at most `b₂`
prefixes (any number of grinding points each). -/
structure AdversaryRA.IBudgetHB (A : AdversaryRA R) (i3 b2 i5 iE : ℕ) : Prop where
  k : SReadsPB (fun t : TbP R => A.keyOf t.1 t.2) i3 b2 i5 iE
  r : ∀ t₀ t₁ : Bytes, SReadsPB (fun t : TbP R => A.respOf t₀ t₁ t.1 t.2) i3 b2 i5 iE

/-- **The key budget gives the prefix budget** (`b₂ = i₂`). -/
lemma AdversaryRA.IBudgetH.toB {A : AdversaryRA R} {i3 i2 i5 iE : ℕ} (h : A.IBudgetH i3 i2 i5 iE) :
    A.IBudgetHB i3 i2 i5 iE where
  k := by
    obtain ⟨Q, hQ, hc⟩ := h.k
    exact ⟨Q, hQ, CardP.cardPB hc⟩
  r t₀ t₁ := by
    obtain ⟨Q, hQ, hc⟩ := h.r t₀ t₁
    exact ⟨Q, hQ, CardP.cardPB hc⟩

end Budget

/-! ## The collision probabilities, counting prefixes -/

section BadPr

variable {Hb : Hashes} {A : AdversaryRA R} {Qk : TbP R → RSP} {Qr : Bytes → Bytes → TbP R → RSP}

/-- **The interaction's `H₂³` read set at the two requests has at most `2b₂` prefixes.** -/
lemma mixQ_pfx {i3 b2 i5 iE : ℕ} (Γ : Tab2G pP) (hck : CardPB Qk i3 b2 i5 iE)
    (hcr : ∀ t₀ t₁, CardPB (Qr t₀ t₁) i3 b2 i5 iE) (t₀ t₁ : Bytes) (sl : SlP)
    (s₂ : Tab5F × (Blk → R)) :
    ((AdversaryRA.mixQ Qk Qr Γ t₀ t₁ sl s₂).image Prod.fst).card ≤ b2 + b2 := by
  classical
  unfold AdversaryRA.mixQ
  rw [image_union]
  exact (card_union_le _ _).trans (add_le_add (hck _).2.2.1 (hcr t₀ t₁ _).2.2.1)

variable {i3 b2 i5 iE : ℕ} (hHb : HashesWF Hb) (hk : ConsP Qk fun t : TbP R => A.keyOf t.1 t.2)
  (hck : CardPB Qk i3 b2 i5 iE)
  (hr : ∀ t₀ t₁, ConsP (Qr t₀ t₁) fun t : TbP R => A.respOf t₀ t₁ t.1 t.2)
  (hcr : ∀ t₀ t₁, CardPB (Qr t₀ t₁) i3 b2 i5 iE)
include hHb hk hck hr hcr

/-- **Session `0`'s collision probability, counting prefixes**: `≤ εcol R i₃ b₂ i₅ i_E`. -/
theorem pr_bad0H_pfx [ZKRow R] [ZK2ARow R] :
    pr ((CH R × Tab2G pP) × Tab2G pP) (fun w => bad0H Hb A Qk Qr w.1.1 w.1.2 w.2) ≤
      εcol R i3 b2 i5 iE := by
  have hck' := hck.cardP
  have hcr' := fun t₀ t₁ => (hcr t₀ t₁).cardP
  rw [← pr_equiv eqB0]
  refine pr_le_of_fst fun ζ => ?_
  obtain ⟨Γ, ⟨ref₀, r₀⟩, x₁⟩ := ζ
  have hI := AdversaryRA.IBudget.subst hk hck' hr hcr' Γ
  have hh := hyp2RA_R hHb hI ref₀ r₀ x₁
  have h := pr_tail2A_pfx Hb (stOf ref₀) (toBA (List.ofFn r₀)) uovM
    (K0 Hb (A.subst Qk Qr Γ) ref₀ r₀ x₁) hh hHb (smallParams_of_le (p := pP) (by decide) (by decide))
    (qf0 Hb A Qk Qr Γ ref₀ r₀ x₁) (fun o1 g s G2 => qf0_h2 Hb Γ ref₀ r₀ x₁ o1 g s G2)
    (fun o1 g s => mixQ_pfx Γ hck hcr _ _ _ _)
    (qf0_rd3 Hb Γ hk hck' hr hcr' ref₀ r₀ x₁) (qf0_rd5 Hb Γ hk hck' hr hcr' ref₀ r₀ x₁)
    (qf0_rdE Hb Γ hk hck' hr hcr' hHb ref₀ r₀ x₁)
  refine le_trans (pr_mono fun a hb => ?_) (h.trans ?_)
  · obtain ⟨⟨ρ, g⟩, G2, s₂⟩ := a
    exact bad0_event hHb ref₀ r₀ x₁ Γ ρ g G2 s₂ hb
  · have m := ZKRow.εz_mono (R := R) pP
      (q3 := i3 + i3 + (i3 + i3) + (i3 + i3)) (q3' := 6 * i3)
      (q5 := i5 + 624 + i5 + (i5 + 624 + i5) + 312 + (i5 + 624 + i5)) (q5' := 6 * i5 + 2184)
      (qE := iE + 4607 + iE + (iE + 4607 + iE) + 4607 + (iE + 4607 + iE)) (qE' := 6 * iE + 18428)
      (by omega) (by omega) (by omega)
    unfold εcol
    show 1 / 2 ^ 113 + ZKRow.εz R pP _ _ _ + ((b2 + b2 : ℕ) : ℝ) / 2 ^ 128 ≤ _
    linarith

/-- **Session `1`'s collision probability, counting prefixes**: `≤ εcol R i₃ b₂ i₅ i_E`. -/
theorem pr_bad1H_pfx [ZKRow R] [ZK2ARow R] :
    pr ((CH R × Tab2G pP) × Tab2G pP) (fun w => bad1H Hb A Qk Qr w.1.1 w.1.2 w.2) ≤
      εcol R i3 b2 i5 iE := by
  have hck' := hck.cardP
  have hcr' := fun t₀ t₁ => (hcr t₀ t₁).cardP
  rw [← pr_equiv eqB1]
  refine pr_le_of_fst fun ζ => ?_
  obtain ⟨Γ, x₀, ref₁, r₁⟩ := ζ
  have hI := AdversaryRA.IBudget.subst hk hck' hr hcr' Γ
  have hh := hyp2RA_R1 Hb hHb hI ref₁ r₁ x₀
  have h := pr_tail2A_pfx Hb (stOf ref₁) (toBA (List.ofFn r₁)) uovM
    (K1R Hb (A.subst Qk Qr Γ) ref₁ r₁ x₀) hh hHb (smallParams_of_le (p := pP) (by decide) (by decide))
    (qf1 Hb A Qk Qr Γ ref₁ r₁ x₀) (fun o1 g s G2 => qf1_h2 Hb Γ ref₁ r₁ x₀ o1 g s G2)
    (fun o1 g s => mixQ_pfx Γ hck hcr _ _ _ _)
    (qf1_rd3 Hb Γ hk hck' hr hcr' ref₁ r₁ x₀) (qf1_rd5 Hb Γ hk hck' hr hcr' ref₁ r₁ x₀)
    (qf1_rdE Hb Γ hk hck' hr hcr' hHb ref₁ r₁ x₀)
  refine le_trans (pr_mono fun a hb => ?_) (h.trans ?_)
  · obtain ⟨⟨ρ, g⟩, G2, s₂⟩ := a
    exact bad1_event hHb ref₁ r₁ x₀ Γ ρ g G2 s₂ hb
  · have m := ZKRow.εz_mono (R := R) pP
      (q3 := i3 + i3 + (i3 + i3) + (i3 + i3)) (q3' := 6 * i3)
      (q5 := i5 + 624 + i5 + (i5 + 624 + i5) + 312 + (i5 + 624 + i5)) (q5' := 6 * i5 + 2184)
      (qE := iE + 4607 + iE + (iE + 4607 + iE) + 4607 + (iE + 4607 + iE)) (qE' := 6 * iE + 18428)
      (by omega) (by omega) (by omega)
    unfold εcol
    show 1 / 2 ^ 113 + ZKRow.εz R pP _ _ _ + ((b2 + b2 : ℕ) : ℝ) / 2 ^ 128 ≤ _
    linarith

/-- **World `false`, the interaction's `H₂³` reads taken out, counting prefixes**
(`G0RA_subst_close` with the collision term `h23W R i₃ b₂ i₅ i_E`). -/
theorem G0RA_subst_close_pfx [ZKRow R] [ZK2ARow R] :
    |pr ((XR × XR) × ShP R) (G0RA Hb A) -
        pr (Tab2G pP × ((XR × XR) × ShP R)) (fun w => G0RA Hb (A.subst Qk Qr w.1) w.2)| ≤
      h23W R i3 b2 i5 iE := by
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
  · -- Without `H₂³` prefixes nothing is patched.
    refine le_of_eq ((pr_congr fun v => iff_false_intro fun hb => ?_).trans pr_false)
    have hc : readH Hb A Qk Qr v.1.1 v.1.2 = ∅ := by
      have := mixQ_pfx v.1.2 hck hcr (tqH Hb A v.1.1 v.1.2).1 (tqH Hb A v.1.1 v.1.2).2
        (slH v.1.1) v.1.1.2
      rw [h0] at this
      exact Finset.image_eq_empty.1 (Finset.card_eq_zero.1 (Nat.le_zero.1 this))
    have hp : patchT (readH Hb A Qk Qr v.1.1 v.1.2) v.1.2 v.2 = v.2 := by
      rw [hc]; funext κ; exact patchT_of_not_mem _ _ (Finset.notMem_empty κ)
    rcases (badH_iff Hb A Qk Qr _ _ _).1 hb with h | h
    · exact h (by rw [hp])
    · exact h (by rw [hp])
  · rw [pr_congr fun v : (CH R × Tab2G pP) × Tab2G pP => badH_iff Hb A Qk Qr v.1.1 v.1.2 v.2]
    have h0' := pr_bad0H_pfx hHb hk hck hr hcr
    have h1' := pr_bad1H_pfx hHb hk hck hr hcr
    have := pr_or_le (fun v : (CH R × Tab2G pP) × Tab2G pP => bad0H Hb A Qk Qr v.1.1 v.1.2 v.2)
      (fun v => bad1H Hb A Qk Qr v.1.1 v.1.2 v.2)
    linarith

end BadPr

/-! ## Blindness, counting prefixes -/

section Blind

/-- **The prefix budget of the Issuer with the roles exchanged.** -/
lemma AdversaryRA.IBudgetHB.swap {A : AdversaryRA R} {i3 b2 i5 iE : ℕ}
    (h : A.IBudgetHB i3 b2 i5 iE) : A.swap.IBudgetHB i3 b2 i5 iE := by
  obtain ⟨Qk, hk, hck⟩ := h.k
  refine ⟨⟨_, AdversaryRA.consP_swapK hk, cardPB_swap hck⟩, fun t₀ t₁ => ?_⟩
  obtain ⟨Qr, hr, hcr⟩ := h.r t₁ t₀
  refine ⟨fun t => AdversaryRA.swapRS (Qr ((t.1.2, t.1.1), t.2)), fun t t' ⟨h1, h2, h3, h4, h5⟩ => ?_,
    cardPB_swap hcr⟩
  obtain ⟨e1, e2⟩ := hr ((t.1.2, t.1.1), t.2) ((t'.1.2, t'.1.1), t'.2) ⟨h2, h1, h3, h4, h5⟩
  exact ⟨by simp only [e1], Prod.ext (congrArg Prod.snd e2) (congrArg Prod.fst e2)⟩

/-- **PomFRIT blindness with an Issuer whose interaction reads every table, `H₂³` included, the
collision term counting prefixes** (for every type of cipher rows): as `blindnessRAH_lean_numG`,
with the interaction's `H₂³` reads bounded by their number of prefixes `b₂` (`IBudgetHB`):

    |Pr[W₀] − Pr[W₁]| ≤ 4·εz(pP; q₃ + 6i₃, q₅ + 6i₅ + 1872, q_E + 6i_E + 23035)
                         + 2·noHitProb + 2·2⁻¹²⁸ + h23H(i₃, b₂, i₅, i_E). -/
theorem blindnessRAH_lean_numG_pfx [ZKRow R] [ZK2ARow R] (A : AdversaryRA R)
    {q3 q5 qE i3 b2 i5 iE : ℕ} (hA : A.GBudget q3 q5 qE) (hI : A.IBudgetHB i3 b2 i5 iE) :
    |pr ((XR × XR) × ShP R) (realGameRA Hashes.shake A false) -
        pr ((XR × XR) × ShP R) (realGameRA Hashes.shake A true)| ≤
      4 * ZKRow.εz R pP (q3 + 6 * i3) (q5 + 6 * i5 + 1872) (qE + 6 * iE + 23035) + 2 * noHitProb +
        2 / 2 ^ 128 + h23H R i3 b2 i5 iE := by
  obtain ⟨Qk, hk, hck⟩ := hI.k
  choose Qr hr hcr using hI.r
  have hk' : ConsP Qk fun t : TbP R => A.keyOf t.1 t.2 := hk
  have hck' : CardPB Qk i3 b2 i5 iE := hck
  have hr' : ∀ t₀ t₁, ConsP (Qr t₀ t₁) fun t : TbP R => A.respOf t₀ t₁ t.1 t.2 := hr
  have hcr' : ∀ t₀ t₁, CardPB (Qr t₀ t₁) i3 b2 i5 iE := hcr
  have h0 : pr ((XR × XR) × ShP R) (realGameRA Hashes.shake A false) =
      pr ((XR × XR) × ShP R) (G0RA Hashes.shake A) := pr_congr (realGameRA_iff Hashes.shake A)
  have h1 : ∀ A' : AdversaryRA R, pr ((XR × XR) × ShP R) (realGameRA Hashes.shake A' true) =
      pr ((XR × XR) × ShP R) (G0RA Hashes.shake A'.swap) := fun A' =>
    (pr_congr (realGameRA_true Hashes.shake A')).trans
      ((pr_equiv swapXR (realGameRA Hashes.shake A'.swap false)).trans
        (pr_congr (realGameRA_iff Hashes.shake A'.swap)))
  -- World `false` and world `true` (the exchanged Issuer, the exchanged read sets).
  have cA := G0RA_subst_close_pfx hashesWF_shake hk' hck' hr' hcr'
  have cS := G0RA_subst_close_pfx (A := A.swap) hashesWF_shake (AdversaryRA.consP_swapK hk')
    (cardPB_swap hck') (AdversaryRA.consP_swapR hr')
    (fun t₀ t₁ => cardPB_swap (hcr' t₁ t₀))
  -- The substituted Issuers satisfy the hypotheses of `blindnessRA_lean_numG`.
  have hck2 := hck'.cardP
  have hcr2 := fun t₀ t₁ => (hcr' t₀ t₁).cardP
  have hmid : |pr (Tab2G pP × ((XR × XR) × ShP R))
        (fun w => G0RA Hashes.shake (A.subst Qk Qr w.1) w.2) -
      pr (Tab2G pP × ((XR × XR) × ShP R))
        (fun w => G0RA Hashes.shake ((A.subst Qk Qr w.1).swap) w.2)| ≤
      4 * ZKRow.εz R pP (q3 + 6 * i3) (q5 + 6 * i5 + 1872) (qE + 6 * iE + 23035) +
        2 * noHitProb + 2 / 2 ^ 128 := by
    refine abs_pr_prod_sub_le _ _ fun Γ => ?_
    have hb := blindnessRA_lean_numG (A.subst Qk Qr Γ)
      (AdversaryRA.GBudget.subst hA hk' hck2 hr' hcr2 Γ)
      (AdversaryRA.IBudget.subst hk' hck2 hr' hcr2 Γ)
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

/-- **PomFRIT blindness with an `H₂³`-reading Issuer, counting prefixes** (function rows, every
term explicit):

    |Pr[W₀] − Pr[W₁]| ≤ 4·εRO(q₃ + 6i₃, q₅ + 6i₅ + 1872, q_E + 6i_E + 23035)
                         + 2·noHitProb + 2·2⁻¹²⁸
                         + [b₂ > 0]·4·(2⁻¹¹³ + εRO(6i₃, 6i₅ + 2184, 6i_E + 18428) + 2b₂·2⁻¹²⁸). -/
theorem blindnessRAH_lean_num_pfx (A : AdversaryRA (Blk → Blk)) {q3 q5 qE i3 b2 i5 iE : ℕ}
    (hA : A.GBudget q3 q5 qE) (hI : A.IBudgetHB i3 b2 i5 iE) :
    |pr ((XR × XR) × ShP (Blk → Blk)) (realGameRA Hashes.shake A false) -
        pr ((XR × XR) × ShP (Blk → Blk)) (realGameRA Hashes.shake A true)| ≤
      4 * εRO (q3 + 6 * i3) (q5 + 6 * i5 + 1872) (qE + 6 * iE + 23035) + 2 * noHitProb +
        2 / 2 ^ 128 +
        (if b2 = 0 then 0 else
          4 * (1 / 2 ^ 113 + εRO (6 * i3) (6 * i5 + 2184) (6 * iE + 18428) +
            (b2 + b2 : ℕ) / 2 ^ 128)) :=
  blindnessRAH_lean_numG_pfx A hA hI

/-- **The same with AES as uniformly random permutations.** -/
theorem blindnessRAH_lean_num_perm_pfx (A : AdversaryRA (Equiv.Perm Blk)) {q3 q5 qE i3 b2 i5 iE : ℕ}
    (hA : A.GBudget q3 q5 qE) (hI : A.IBudgetHB i3 b2 i5 iE) :
    |pr ((XR × XR) × ShP (Equiv.Perm Blk)) (realGameRA Hashes.shake A false) -
        pr ((XR × XR) × ShP (Equiv.Perm Blk)) (realGameRA Hashes.shake A true)| ≤
      4 * εROPm pP (q3 + 6 * i3) (q5 + 6 * i5 + 1872) (qE + 6 * iE + 23035) + 2 * noHitProb +
        2 / 2 ^ 128 +
        (if b2 = 0 then 0 else
          4 * (1 / 2 ^ 113 + εROPm pP (6 * i3) (6 * i5 + 2184) (6 * iE + 18428) +
            (b2 + b2 : ℕ) / 2 ^ 128)) :=
  blindnessRAH_lean_numG_pfx A hA hI

end Blind

end VoleMole.Privacy.PomFRIT
