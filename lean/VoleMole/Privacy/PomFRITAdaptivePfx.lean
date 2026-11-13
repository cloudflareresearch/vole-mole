import VoleMole.Privacy.PomFRITAdaptive
import VoleMole.Privacy.PomFRITRAHPfx

/-!
# Adaptive PomFRIT blindness, the collision term counting prefixes

`blindnessAd_lean_num` (`Privacy/PomFRITAdaptive.lean`) applies `blindnessRAH_lean_numG` to the
reduction whose interaction runs the further sessions, with its `H₂³` budget counted in keys:
`(m₁ + m₂)·2³²`, the grinding points of the sessions run inside it. The collision term then
charges `2⁻¹²⁸` per key, `2⁻⁹⁶` per session. But each session reads `H₂³` at the `2³²` points
of **one** prefix (`fullKeys`: `univ.image (key2 pP pre)`), so with
`blindnessRAH_lean_numG_pfx` (`Privacy/PomFRITRAHPfx.lean`) it is charged once.

* `SReadsB`: `SReads` with the `H₂³` read sets bounded by their number of prefixes; `const`,
  `mono`, `bind`, `map` as for `SReads`.
* `fullX_sreadsB`: a whole further session reads `H₂³` at keys of at most one prefix (the same read
  sets as `fullX_sreads`); `runSeq_sreadsB`: sequential sessions, `|cs|` prefixes.
* `AdversaryAd.red_iBudgetHB`: the reduction's interaction budget `IBudgetHB 0 (m₁ + m₂)
  ((m₁+m₂)·624) ((m₁+m₂)·4607)`.
* **`blindnessAd_lean_numG_pfx`**, **`blindnessAd_lean_num_pfx`**,
  **`blindnessAd_lean_num_perm_pfx`**: the bounds of `blindnessAd_lean_numG`, `_num`, `_num_perm`
  with `m₁ + m₂` (prefixes) in place of `(m₁ + m₂)·2³²` (keys) in the collision term.
* **`blindnessAd_lean_le_pfx`**: with `n = m₁ + m₂ + m₃ + 2` sessions in all,
  `≤ n·2⁻¹⁰² + 4·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸` (against `n·2⁻⁹²`): `2⁻⁸²` for `n ≤ 2²⁰`
  (`blindnessAd_lean_2pow20_pfx`), `2⁻⁷⁰` for `n ≤ 2³²` (`blindnessAd_lean_2pow32_pfx`), the
  numbers of the non-adaptive schedule (`blindnessN_lean_le`, `n·2⁻¹⁰³`) up to a factor 2.
  Per session, the main term pays `4·(7·624 + 221·7·4607)·2⁻¹²⁸ ≈ 2⁻¹⁰³·²` (the session's reads,
  once in the guess and six times through the interaction) and the collision term
  `4·(6·624 + 221·6·4607 + 2)·2⁻¹²⁸ ≈ 2⁻¹⁰³·⁵` (its reads in the second zero-knowledge
  application, and `2·2⁻¹²⁸` for its prefix).
-/

open Finset

set_option synthInstance.maxSize 1024

set_option linter.unusedSectionVars false

namespace VoleMole.Privacy.PomFRIT

open VoleMole.Verifier VoleMole.Verifier.Bridge VoleMole.ZK VoleMole.ZK.Sim VoleMole.Arith
open VoleMole.Spec VoleMole.Spec.PomFRIT

attribute [local irreducible] commitRefresher UOVKey.eval

variable {R : Type} [Fintype R] [Nonempty R] [CipherRow R]

/-! ## Consistent readers, `H₂³` by prefixes -/

section SReadsB

variable {p : Params} {X Y : Type*}

/-- **A consistent table reader whose `H₂³` reads have at most `b₂` prefixes** (`SReads` with the
number of prefixes `(Q t).2.1.image Prod.fst` in place of the number of `H₂³` keys). -/
def SReadsB (p : Params) (S : Tb R p → X) (s3 b2 s5 sE : ℕ) : Prop :=
  ∃ Q : Tb R p → RS p, (∀ t t', AgT (Q t) t t' → Q t' = Q t ∧ S t' = S t) ∧
    ∀ t, (Q t).1.card ≤ s3 ∧ ((Q t).2.1.image Prod.fst).card ≤ b2 ∧ (Q t).2.2.1.card ≤ s5 ∧
      (Q t).2.2.2.card ≤ sE

lemma SReadsB.const (x : X) : SReadsB p (fun _ : Tb R p => x) 0 0 0 0 :=
  ⟨fun _ => (∅, ∅, ∅, ∅), fun _ _ _ => ⟨rfl, rfl⟩, fun _ => by simp⟩

lemma SReadsB.mono {f : Tb R p → X} {a3 a2 a5 aE b3 b2 b5 bE : ℕ} (h : SReadsB p f a3 a2 a5 aE)
    (h3 : a3 ≤ b3) (h2 : a2 ≤ b2) (h5 : a5 ≤ b5) (hE : aE ≤ bE) : SReadsB p f b3 b2 b5 bE := by
  obtain ⟨Q, hQ, hc⟩ := h
  exact ⟨Q, hQ, fun t => ⟨(hc t).1.trans h3, (hc t).2.1.trans h2, (hc t).2.2.1.trans h5,
    (hc t).2.2.2.trans hE⟩⟩

/-- **Sequencing**: the prefixes of the union are the union of the prefixes. -/
lemma SReadsB.bind {f : Tb R p → Y} {g : Y → Tb R p → X} {a3 a2 a5 aE b3 b2 b5 bE : ℕ}
    (hf : SReadsB p f a3 a2 a5 aE) (hg : ∀ y, SReadsB p (g y) b3 b2 b5 bE) :
    SReadsB p (fun t => g (f t) t) (a3 + b3) (a2 + b2) (a5 + b5) (aE + bE) := by
  classical
  obtain ⟨Qf, hQf, hcf⟩ := hf
  choose Qg hQg hcg using hg
  refine ⟨fun t => (Qf t).union (Qg (f t) t), fun t t' h => ?_, fun t => ?_⟩
  · obtain ⟨e1, e2⟩ := hQf t t' h.left
    obtain ⟨e3, e4⟩ := hQg (f t) t t' h.right
    refine ⟨?_, ?_⟩
    · show (Qf t').union (Qg (f t') t') = (Qf t).union (Qg (f t) t)
      rw [e1, e2, e3]
    · show g (f t') t' = g (f t) t
      rw [e2, e4]
  · obtain ⟨a1, a2', a3', a4⟩ := hcf t
    obtain ⟨b1, b2', b3', b4⟩ := hcg (f t) t
    refine ⟨(card_union_le _ _).trans (add_le_add a1 b1), ?_,
      (card_union_le _ _).trans (add_le_add a3' b3'), (card_union_le _ _).trans (add_le_add a4 b4)⟩
    show (((Qf t).2.1 ∪ (Qg (f t) t).2.1).image Prod.fst).card ≤ a2 + b2
    rw [image_union]
    exact (card_union_le _ _).trans (add_le_add a2' b2')

lemma SReadsB.map {f : Tb R p → Y} {a3 a2 a5 aE : ℕ} (hf : SReadsB p f a3 a2 a5 aE) (φ : Y → X) :
    SReadsB p (fun t => φ (f t)) a3 a2 a5 aE := by
  simpa using hf.bind (g := fun y _ => φ y) fun y => SReadsB.const (φ y)

/-- A consistent reader of the shared tables alone is a joint consistent reader of both challenge
slices and the shared tables, with the same prefixes. -/
lemma SReadsPB.of_shared {f : ShP R → X} {b2 a5 aE : ℕ}
    (h : SReadsB pP (fun t : Tb R pP => f t.2) 0 b2 a5 aE) (a3 : ℕ) :
    SReadsPB (fun t : TbP R => f t.2) a3 b2 a5 aE := by
  obtain ⟨Q, hQ, hc⟩ := h
  refine ⟨fun t => ((∅, ∅), (Q (default, t.2)).2), fun t t' h => ?_, fun t => ?_⟩
  · obtain ⟨-, -, h2, h5, hE⟩ := h
    obtain ⟨e1, e2⟩ := hQ (default, t.2) (default, t'.2) ⟨fun _ _ => rfl, h2, h5, hE⟩
    exact ⟨by simp only [e1], e2⟩
  · obtain ⟨-, c2, c5, cE⟩ := hc (default, t.2)
    exact ⟨by simp, by simp, c2, c5, cE⟩

end SReadsB

/-! ## A whole further session reads one prefix -/

section Full

variable {Hb : Hashes}

/-- **A whole further session's `H₂³` reads have at most one prefix**: the grinding points of its
own prefix, or none. -/
lemma fullKeys_pfx (pk : UOVKey) (msg : Bytes) (ρ : Bytes → Bytes) (x : XR) (s : ShP R) :
    ((fullKeys (R := R) (Hb := Hb) pk msg ρ x s).2.1.image Prod.fst).card ≤ 1 := by
  unfold fullKeys
  split_ifs
  · refine card_le_one.2 fun a ha b hb => ?_
    obtain ⟨κ, hκ, rfl⟩ := mem_image.1 ha
    obtain ⟨κ', hκ', rfl⟩ := mem_image.1 hb
    obtain ⟨c, -, rfl⟩ := mem_image.1 hκ
    obtain ⟨c', -, rfl⟩ := mem_image.1 hκ'
    rfl
  · simp

/-- **A whole further session is a consistent reader** of `H₅` (`624` keys), the cipher (`4607`)
and `H₂³` at keys of **one** prefix (its grinding block, if its response passes the checks). The
read sets are those of `fullX_sreads`. -/
theorem fullX_sreadsB (hHb : HashesWF Hb) (pk : UOVKey) (msg : Bytes) (ρ : Bytes → Bytes) (x : XR) :
    SReadsB pP (fun t : Tb R pP => fullX Hb pk msg ρ x t.2) 0 1 624 4607 := by
  classical
  refine ⟨fun t => fullKeys (Hb := Hb) pk msg ρ x t.2, fun t t' h => ?_, fun t => ⟨by simp [fullKeys],
    fullKeys_pfx pk msg ρ x t.2, (s1Keys_card (Hb := Hb) x t.2).1, (s1Keys_card (Hb := Hb) x t.2).2⟩⟩
  obtain ⟨-, h2, h5, hE⟩ := h
  obtain ⟨g, G2, s₂⟩ := t
  obtain ⟨g', G2', s₂'⟩ := t'
  dsimp only at h2 h5 hE ⊢
  obtain ⟨e5, eE, eS, eT⟩ := full_step1 hHb pk msg ρ x (G2, s₂) (G2', s₂') h5 hE
  have eP := preX_cons hHb pk msg ρ x (G2, s₂) (G2', s₂') h5 hE
  refine ⟨?_, ?_⟩
  · unfold fullKeys
    rw [eT, eP, e5, eE]
  · unfold fullX
    rw [sessX_eq_tR pk msg ρ x (G2', s₂'), sessX_eq_tR pk msg ρ x (G2, s₂)]
    dsimp only
    rw [eT]
    refine Prod.ext rfl ?_
    dsimp only
    cases hv : validB (respAdv (R := R) pk msg ρ) (ρ (tR Hb (respAdv pk msg ρ) msg x (G2, s₂)))
        (tR Hb (respAdv pk msg ρ) msg x (G2, s₂))
    · exact finish_of_not_valid (respAdv pk msg ρ) _ _ _ _ hv
    · rw [sigR_tables hHb _ msg x (G2, s₂) (G2', s₂') eS]
      dsimp only
      rw [sigR_h23 hHb pk msg ρ x G2 G2' s₂ hv fun κ hκ => h2 κ (by
        unfold fullKeys; rw [hv]; exact hκ)]

/-- **Sequential sessions are a consistent reader**, `H₂³` at `|cs|` prefixes. -/
theorem runSeq_sreadsB (hHb : HashesWF Hb) (next : List Hist → UOVKey × Bytes)
    (resp : List Hist → Bytes → Bytes) (cs : List XR) :
    ∀ H, SReadsB pP (fun t : Tb R pP => runSeq Hb next resp cs H t.2) 0 cs.length
      (cs.length * 624) (cs.length * 4607) := by
  induction cs with
  | nil => intro H; simpa [runSeq] using SReadsB.const (R := R) (p := pP) H
  | cons x cs ih =>
    intro H
    have h := (fullX_sreadsB (R := R) hHb (next H).1 (next H).2 (resp H) x).bind
      (g := fun y (t : Tb R pP) => runSeq Hb next resp cs (H ++ [y]) t.2) fun y => ih (H ++ [y])
    refine (h.mono le_rfl ?_ ?_ ?_)
    · simp only [List.length_cons]; omega
    · simp only [List.length_cons]; omega
    · simp only [List.length_cons]; omega

end Full

/-! ## The reduction's prefix budget -/

section Red

variable {Hb : Hashes} {m₁ m₂ m₃ : ℕ}

/-- **The reduction's interaction budget, `H₂³` by prefixes**: one prefix per further session run
inside the interaction (`m₁` in the key stage, `m₁ + m₂` in the response stage). -/
theorem AdversaryAd.red_iBudgetHB (hHb : HashesWF Hb) (A : AdversaryAd R) (c : TapesAd m₁ m₂ m₃) :
    (A.red Hb c).IBudgetHB 0 (m₁ + m₂) ((m₁ + m₂) * 624) ((m₁ + m₂) * 4607) where
  k := by
    have h := (runSeq_sreadsB (R := R) hHb A.next₁ A.resp₁ (List.ofFn c.1) []).map
      fun H => (A.pk H, A.msg H false, A.msg H true)
    simp only [List.length_ofFn] at h
    exact SReadsPB.of_shared (f := fun s => (A.red Hb c).keyOf (default, default) s)
      ((h.mono le_rfl (Nat.le_add_right _ _)
        (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
        (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))) 0
  r t₀ t₁ := by
    have h := (runSeq_sreadsB (R := R) hHb A.next₁ A.resp₁ (List.ofFn c.1) []).bind
      (g := fun H₁ (t : Tb R pP) =>
        (A.respond H₁ t₀ t₁ (runSeq Hb (A.next₂ H₁ t₀ t₁) (A.resp₂ H₁ t₀ t₁) (List.ofFn c.2.1) [] t.2) false,
          A.respond H₁ t₀ t₁ (runSeq Hb (A.next₂ H₁ t₀ t₁) (A.resp₂ H₁ t₀ t₁) (List.ofFn c.2.1) [] t.2) true))
      fun H₁ => (runSeq_sreadsB (R := R) hHb (A.next₂ H₁ t₀ t₁) (A.resp₂ H₁ t₀ t₁) (List.ofFn c.2.1) []).map
        fun H₂ => (A.respond H₁ t₀ t₁ H₂ false, A.respond H₁ t₀ t₁ H₂ true)
    simp only [List.length_ofFn] at h
    exact SReadsPB.of_shared (f := fun s => (A.red Hb c).respOf t₀ t₁ (default, default) s)
      ((h.mono le_rfl le_rfl (by rw [Nat.add_mul]) (by rw [Nat.add_mul]))) 0

end Red

/-! ## The bound -/

section Bound

variable {m₁ m₂ m₃ : ℕ}

/-- **PomFRIT blindness with adaptively scheduled further sessions, the collision term counting
prefixes, for every type of cipher rows**: as `blindnessAd_lean_numG`, with `m₁ + m₂` prefixes in
place of `(m₁ + m₂)·2³²` keys:

    |Pr[W₀] − Pr[W₁]| ≤ 4·εz(pP; q₃, q₅ + (m₁+m₂+m₃)·624 + 6(m₁+m₂)·624 + 1872,
                                  q_E + (m₁+m₂+m₃)·4607 + 6(m₁+m₂)·4607 + 23035)
                         + 2·noHitProb + 2·2⁻¹²⁸ + h23H(0, m₁+m₂, (m₁+m₂)·624, (m₁+m₂)·4607). -/
theorem blindnessAd_lean_numG_pfx [ZKRow R] [ZK2ARow R] (A : AdversaryAd R) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) :
    |pr (((XR × XR) × TapesAd m₁ m₂ m₃) × ShP R) (realGameAd Hashes.shake A false) -
        pr (((XR × XR) × TapesAd m₁ m₂ m₃) × ShP R) (realGameAd Hashes.shake A true)| ≤
      4 * ZKRow.εz R pP (q3 + 6 * 0) ((m₁ + m₂ + m₃) * 624 + q5 + 6 * ((m₁ + m₂) * 624) + 1872)
          ((m₁ + m₂ + m₃) * 4607 + qE + 6 * ((m₁ + m₂) * 4607) + 23035) + 2 * noHitProb +
        2 / 2 ^ 128 + h23H R 0 (m₁ + m₂) ((m₁ + m₂) * 624) ((m₁ + m₂) * 4607) := by
  rw [← pr_equiv tapeAd, ← pr_equiv tapeAd]
  exact abs_pr_prod_sub_le _ _ fun c =>
    blindnessRAH_lean_numG_pfx (A.red Hashes.shake c) (A.red_gBudget hashesWF_shake hA c)
      (A.red_iBudgetHB hashesWF_shake c)

/-- **PomFRIT blindness with adaptively scheduled further sessions, counting prefixes** (function
rows). -/
theorem blindnessAd_lean_num_pfx (A : AdversaryAd (Blk → Blk)) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) :
    |pr (((XR × XR) × TapesAd m₁ m₂ m₃) × ShP (Blk → Blk)) (realGameAd Hashes.shake A false) -
        pr (((XR × XR) × TapesAd m₁ m₂ m₃) × ShP (Blk → Blk)) (realGameAd Hashes.shake A true)| ≤
      4 * εRO (q3 + 6 * 0) ((m₁ + m₂ + m₃) * 624 + q5 + 6 * ((m₁ + m₂) * 624) + 1872)
          ((m₁ + m₂ + m₃) * 4607 + qE + 6 * ((m₁ + m₂) * 4607) + 23035) + 2 * noHitProb +
        2 / 2 ^ 128 +
        (if m₁ + m₂ = 0 then 0 else
          4 * (1 / 2 ^ 113 + εRO (6 * 0) (6 * ((m₁ + m₂) * 624) + 2184) (6 * ((m₁ + m₂) * 4607) + 18428) +
            (m₁ + m₂ + (m₁ + m₂) : ℕ) / 2 ^ 128)) :=
  blindnessAd_lean_numG_pfx A hA

/-- **The same with AES as uniformly random permutations.** -/
theorem blindnessAd_lean_num_perm_pfx (A : AdversaryAd (Equiv.Perm Blk)) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) :
    |pr (((XR × XR) × TapesAd m₁ m₂ m₃) × ShP (Equiv.Perm Blk)) (realGameAd Hashes.shake A false) -
        pr (((XR × XR) × TapesAd m₁ m₂ m₃) × ShP (Equiv.Perm Blk)) (realGameAd Hashes.shake A true)| ≤
      4 * εROPm pP (q3 + 6 * 0) ((m₁ + m₂ + m₃) * 624 + q5 + 6 * ((m₁ + m₂) * 624) + 1872)
          ((m₁ + m₂ + m₃) * 4607 + qE + 6 * ((m₁ + m₂) * 4607) + 23035) + 2 * noHitProb +
        2 / 2 ^ 128 + h23H (Equiv.Perm Blk) 0 (m₁ + m₂) ((m₁ + m₂) * 624) ((m₁ + m₂) * 4607) :=
  blindnessAd_lean_numG_pfx A hA

/-- **The adaptive bound in numbers, counting prefixes**: with `n = m₁ + m₂ + m₃ + 2` sessions in
all,

    |Pr[W₀] − Pr[W₁]| ≤ n·2⁻¹⁰² + 4·(q₃ + q₅ + 221·q_E)·2⁻¹²⁸.

Per session `≤ 4·(7·624 + 221·7·4607 + 6·624 + 221·6·4607 + 2)·2⁻¹²⁸ ≈ 2⁻¹⁰²·³`; the constant
(`2·2⁻¹⁰²` covers it) is the two challenge sessions' and the `2⁻¹¹³` terms. -/
theorem blindnessAd_lean_le_pfx (A : AdversaryAd (Blk → Blk)) {q3 q5 qE : ℕ} (hA : A.Budget q3 q5 qE) :
    |pr (((XR × XR) × TapesAd m₁ m₂ m₃) × ShP (Blk → Blk)) (realGameAd Hashes.shake A false) -
        pr (((XR × XR) × TapesAd m₁ m₂ m₃) × ShP (Blk → Blk)) (realGameAd Hashes.shake A true)| ≤
      (m₁ + m₂ + m₃ + 2 : ℕ) / 2 ^ 102 + 4 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 := by
  have h := blindnessAd_lean_num_pfx (m₁ := m₁) (m₂ := m₂) (m₃ := m₃) A hA
  have hn := noHitProb_le_128
  have e : ∀ x : ℝ, x / 2 ^ 102 = x * 67108864 / 2 ^ 128 := fun x => by
    rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  have e113 : (1 : ℝ) / 2 ^ 113 = 32768 / 2 ^ 128 := by
    rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  have h1 : (0 : ℝ) ≤ m₁ := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ m₂ := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ m₃ := Nat.cast_nonneg _
  unfold εRO at h
  rw [e113] at h
  split_ifs at h with h0
  · push_cast at h ⊢
    rw [e]
    linarith
  · push_cast at h ⊢
    rw [e]
    linarith

/-- **`2²⁰` sessions, counting prefixes**: `≤ 2⁻⁸²` plus the guess's budget terms. -/
theorem blindnessAd_lean_2pow20_pfx (A : AdversaryAd (Blk → Blk)) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) (hn : m₁ + m₂ + m₃ + 2 ≤ 2 ^ 20) :
    |pr (((XR × XR) × TapesAd m₁ m₂ m₃) × ShP (Blk → Blk)) (realGameAd Hashes.shake A false) -
        pr (((XR × XR) × TapesAd m₁ m₂ m₃) × ShP (Blk → Blk)) (realGameAd Hashes.shake A true)| ≤
      1 / 2 ^ 82 + 4 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 := by
  have h := blindnessAd_lean_le_pfx (m₁ := m₁) (m₂ := m₂) (m₃ := m₃) A hA
  have : ((m₁ + m₂ + m₃ + 2 : ℕ) : ℝ) ≤ 2 ^ 20 := by exact_mod_cast hn
  have h2 : ((m₁ + m₂ + m₃ + 2 : ℕ) : ℝ) / 2 ^ 102 ≤ 1 / 2 ^ 82 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

/-- **`2³²` sessions, counting prefixes**: `≤ 2⁻⁷⁰` plus the guess's budget terms. -/
theorem blindnessAd_lean_2pow32_pfx (A : AdversaryAd (Blk → Blk)) {q3 q5 qE : ℕ}
    (hA : A.Budget q3 q5 qE) (hn : m₁ + m₂ + m₃ + 2 ≤ 2 ^ 32) :
    |pr (((XR × XR) × TapesAd m₁ m₂ m₃) × ShP (Blk → Blk)) (realGameAd Hashes.shake A false) -
        pr (((XR × XR) × TapesAd m₁ m₂ m₃) × ShP (Blk → Blk)) (realGameAd Hashes.shake A true)| ≤
      1 / 2 ^ 70 + 4 * (q3 + q5 + 221 * qE : ℕ) / 2 ^ 128 := by
  have h := blindnessAd_lean_le_pfx (m₁ := m₁) (m₂ := m₂) (m₃ := m₃) A hA
  have : ((m₁ + m₂ + m₃ + 2 : ℕ) : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hn
  have h2 : ((m₁ + m₂ + m₃ + 2 : ℕ) : ℝ) / 2 ^ 102 ≤ 1 / 2 ^ 70 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

end Bound

end VoleMole.Privacy.PomFRIT
