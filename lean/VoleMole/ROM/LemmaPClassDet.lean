import VoleMole.ROM.LemmaPClass
import VoleMole.Verifier.Bridge.MaskSlices

/-!
# Lemma P with the class extractor, at a chain of the executable verifier

`lean/docs/security/pomfrit-lemmap-tight.md` §6A. `ROM/LemmaPClass.lean` proves the per-chain step
of Lemma P^cls with the affine and two-label structure of the response as hypotheses
(`class_or_small_dec`). `Verifier/Bridge/MaskSlices.lean` proves that structure for the executable
verifier. This file puts them together.

* **The decoder's data** for the class of a tree `i`, as functions of the alive trees `S`, the
  class keys and the blocks `hd` of the other trees: the directions `treeDirs i` (the challenges
  supported on tree `i`: a subgroup of at least `2⁷` directions of the class), the trees `clsT1`
  (the alive trees outside the class with the label rows of the widest class), the generators
  `genOf` (the unit vectors of their blocks) and the base points
  `Seed.basePts` (the challenges of the slice that vanish on the class and on `clsT1`).
* **The certificate** `clsCert`: the decoder has a candidate, a direction `δ`, a base point `r`
  and a set `s` of generators whose predicted increment of the check value is `0`
  (`Seed.decCand`). It reads the check value at the points `Seed.decPts` only. For the
  executable verifier the prediction is exact (`chain_twoLabelOn`), so a candidate is a pair of
  challenges with the same check value: `clsCert_iff_dec`. The decoder of `Seed/SliceDecode.lean`
  checks its candidate with two more evaluations; here that check always passes.
* **`pomfritT_extract_class_chain`**: `pomfritT_extract_major_chain` with the class extractor and
  `2⁵⁰`. For a chain of the executable verifier with PomFRIT's parameters, a `chal1` that is
  KOS-good and good for parallelism (`Seed.KOSPar` on `Seed.DisjQuads`), and an accepting set whose
  blocks outside `S` are `hd`: some tree of `S` has a candidate in the relation whose prefix is
  `clsExt`'s output, or at most `2⁵⁰` admissible `chal3` are accepted. No hypothesis on the
  response: `AffineOn`, `TwoLabelOn` and the label rows' tree form are proved.

No `sorry`, no `axiom`.
-/

open Finset

-- `Finset.univ : Finset Blocks` needs a deeper recursion limit in the unifier.
set_option maxRecDepth 8000

namespace VoleMole.PomFRIT

open VoleMole.SeedExtraction VoleMole.Seed VoleMole.Arith VoleMole.Verifier
  VoleMole.Verifier.Bridge VoleMole.EndToEnd

/-! ## The decoder's data -/

section Data

open Classical in
/-- The challenges supported on tree `i`. -/
noncomputable def treeDirs (i : Fin BAVC.tau) : Finset Blocks :=
  Finset.univ.filter fun δ => ∀ k, k ≠ i → δ k = 0

open Classical in
lemma mem_treeDirs {i : Fin BAVC.tau} {δ : Blocks} : δ ∈ treeDirs i ↔ ∀ k, k ≠ i → δ k = 0 := by
  unfold treeDirs
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

lemma treeDirs_add {i : Fin BAVC.tau} {a b : Blocks} (ha : a ∈ treeDirs i) (hb : b ∈ treeDirs i) :
    a + b ∈ treeDirs i :=
  mem_treeDirs.2 fun k hk => by
    simp [mem_treeDirs.1 ha k hk, mem_treeDirs.1 hb k hk]

lemma treeDirs_dirs {i : Fin BAVC.tau} {C : Finset (Fin BAVC.tau)} (hi : i ∈ C) {δ : Blocks}
    (hδ : δ ∈ treeDirs i) : δ ∈ dirs C := fun k hk =>
  mem_treeDirs.1 hδ k fun h => hk (h ▸ hi)

lemma card_treeDirs (i : Fin BAVC.tau) : (treeDirs i).card = 2 ^ width i := by
  classical
  rw [← card_block i, ← Finset.card_univ]
  symm
  refine Finset.card_bij (fun x _ => Pi.single i x) (fun x _ => mem_treeDirs.2 fun k hk => by
    simp [Pi.single_eq_of_ne hk]) (fun x _ y _ h => Pi.single_injective i h) fun δ hδ =>
    ⟨δ i, Finset.mem_univ _, ?_⟩
  funext k
  by_cases hk : k = i
  · subst hk; simp
  · rw [Pi.single_eq_of_ne hk, mem_treeDirs.1 hδ k hk]

lemma seven_le_width (i : Fin 17) : 7 ≤ width i := by unfold width; split <;> omega

lemma width_le_eight (i : Fin 17) : width i ≤ 8 := by unfold width; split <;> omega

/-- The index of a bit of the challenge: a tree and a bit of its block. -/
abbrev GenIdx := Σ i : Fin BAVC.tau, Fin (BAVC.kOf i)

/-- The number of bits of the challenge (120). -/
abbrev nGen : ℕ := Fintype.card GenIdx

/-- The unit vector of the bit `x`. -/
def unitVec (x : GenIdx) : Blocks := Pi.single x.1 (Pi.single x.2 1)

/-- The decoder's generators for the trees `T₁`: the unit vectors of their blocks (and `0` for
the other bits). -/
noncomputable def genOf (T₁ : Finset (Fin BAVC.tau)) (k : Fin nGen) : Blocks :=
  if ((Fintype.equivFin GenIdx).symm k).1 ∈ T₁ then unitVec ((Fintype.equivFin GenIdx).symm k)
  else 0

lemma genOf_mem_dirs (T₁ : Finset (Fin BAVC.tau)) (k : Fin nGen) : genOf T₁ k ∈ dirs T₁ := by
  intro i hi
  unfold genOf
  split
  · rename_i h
    have hne : i ≠ ((Fintype.equivFin GenIdx).symm k).1 := fun e => hi (e ▸ h)
    simp [unitVec, Pi.single_eq_of_ne hne]
  · rfl

/-- A challenge is the sum of the unit vectors of its nonzero bits. -/
lemma eq_sum_unitVec (v : Blocks) :
    v = ∑ x ∈ (Finset.univ : Finset GenIdx).filter (fun x => v x.1 x.2 = 1), unitVec x := by
  classical
  have h01 : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
  funext i b
  rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_filter]
  rw [Finset.sum_eq_single (⟨i, b⟩ : GenIdx)]
  · rcases h01 (v i b) with h | h <;> simp [unitVec, h]
  · rintro ⟨i', b'⟩ - hne
    split
    · by_cases hi : i' = i
      · subst hi
        have hb : b' ≠ b := fun e => hne (by rw [e])
        simp [unitVec, Pi.single_eq_of_ne hb.symm]
      · simp [unitVec, Pi.single_eq_of_ne (Ne.symm hi)]
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h

lemma genOf_span (T₁ : Finset (Fin BAVC.tau)) (v : Blocks) (hv : v ∈ dirs T₁) :
    ∃ s : Finset (Fin nGen), v = ∑ k ∈ s, genOf T₁ k := by
  classical
  refine ⟨((Finset.univ : Finset GenIdx).filter (fun x => v x.1 x.2 = 1)).map
    (Fintype.equivFin GenIdx).toEmbedding, ?_⟩
  rw [Finset.sum_map]
  conv_lhs => rw [eq_sum_unitVec v]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx1 : v x.1 x.2 = 1 := (Finset.mem_filter.1 hx).2
  have hT : x.1 ∈ T₁ := by
    by_contra h
    rw [hv x.1 h] at hx1
    exact absurd hx1 (by simp)
  simp [genOf, hT]

/-- The challenges with the blocks `hd` outside `S`. -/
abbrev sliceOf (S : Finset (Fin BAVC.tau)) (hd : Blocks) : Set Blocks :=
  {Δ : Blocks | ∀ k ∉ S, Δ k = hd k}

variable {Kt Kl : Type*} [DecidableEq Kt] [DecidableEq Kl]

/-- The class of tree `i`: the trees of `S` with its key. -/
def clsOf (S : Finset (Fin BAVC.tau)) (key : Fin BAVC.tau → Kt) (i : Fin BAVC.tau) :
    Finset (Fin BAVC.tau) :=
  S.filter fun k => key k = key i

/-- The trees whose blocks are the decoder's linear unknowns for the class of `i`: the trees of
`S` outside the class with the label rows of the widest class. -/
def clsT1 (S : Finset (Fin BAVC.tau)) (key : Fin BAVC.tau → Kt) (lab : Fin BAVC.tau → Kl)
    (i : Fin BAVC.tau) : Finset (Fin BAVC.tau) :=
  S.filter fun k => key k ≠ key i ∧ lab k = lab ((majTree S key).getD i)

lemma mem_clsOf {S : Finset (Fin BAVC.tau)} {key : Fin BAVC.tau → Kt} {i k : Fin BAVC.tau} :
    k ∈ clsOf S key i ↔ k ∈ S ∧ key k = key i := Finset.mem_filter

lemma self_mem_clsOf {S : Finset (Fin BAVC.tau)} {key : Fin BAVC.tau → Kt} {i : Fin BAVC.tau}
    (hi : i ∈ S) : i ∈ clsOf S key i := mem_clsOf.2 ⟨hi, rfl⟩

lemma mem_clsT1 {S : Finset (Fin BAVC.tau)} {key : Fin BAVC.tau → Kt} {lab : Fin BAVC.tau → Kl}
    {i k : Fin BAVC.tau} :
    k ∈ clsT1 S key lab i ↔ k ∈ S ∧ key k ≠ key i ∧ lab k = lab ((majTree S key).getD i) :=
  Finset.mem_filter

lemma clsOf_disjoint_clsT1 (S : Finset (Fin BAVC.tau)) (key : Fin BAVC.tau → Kt)
    (lab : Fin BAVC.tau → Kl) (i : Fin BAVC.tau) :
    Disjoint (clsOf S key i) (clsT1 S key lab i) :=
  Finset.disjoint_filter.2 fun _ _ h1 h2 => h2.1 h1

end Data

/-! ## Candidates and pairs (generic) -/

section CandGeneric

variable {X M : Type*} [AddCommGroup X] [AddCommGroup M] [DecidableEq X] {n : ℕ}

/-- If the predictions are exact, the decoder has a candidate iff it outputs a pair. -/
theorem exists_decCand_iff_dec {K : X → M} {U Rs : Finset X} {gen : Fin n → X}
    (hTL : ∀ δ ∈ U, ∀ r ∈ Rs, ∀ s, incr K δ (decPt gen r s) = decPred K gen δ r s) :
    (∃ t, decCand K U Rs gen t) ↔ (dec K U Rs gen).isSome := by
  constructor
  · rintro ⟨⟨δ, r, s⟩, hδ, hr, hpred⟩
    refine dec_complete hTL ⟨δ, hδ, r, hr, s, ?_⟩
    have := hTL δ hδ r hr s
    rw [hpred, incr, sub_eq_zero] at this
    exact this
  · intro h
    by_contra hno
    simp [dec, decOf, hno] at h

end CandGeneric

section PredGeneric

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F] [Fintype F] [DecidableEq F]
variable {B : ι → Type*} [∀ i, AddCommGroup (B i)] [∀ i, DecidableEq (B i)] {n : ℕ}

/-- For a two-label response the decoder's predictions of the check value are exact. -/
theorem decPred_exact_of_twoLabel {T : Finset F} {L : ℕ} (c : Ch F T) (e : (∀ i, B i) →+ F)
    {Q : (∀ i, B i) → Fin L → F} {D : (∀ i, B i) → Fin 4 → F} (ũ : Fin 4 → F)
    {Sb : Set (∀ i, B i)} {C T₁ : Finset ι} (htl : TwoLabelOn Sb C T₁ Q D)
    {U Rs : Finset (∀ i, B i)} {gen : Fin n → ∀ i, B i} (hU : ∀ δ ∈ U, δ ∈ dirs C)
    (hgen : ∀ k, gen k ∈ dirs T₁) (hRs : ∀ r ∈ Rs, r ∈ Sb) :
    ∀ δ ∈ U, ∀ r ∈ Rs, ∀ s, incr (kosValue c e Q D ũ) δ (decPt gen r s) =
      decPred (kosValue c e Q D ũ) gen δ r s := by
  intro δ hδ r hr s
  refine incr_decPt (fun s k => ?_) s
  obtain ⟨hQ, hD⟩ := htl r (hRs r hr) δ (hU δ hδ) _ (sum_mem_dirs hgen s) _ (hgen k)
  exact incr_kosValue_twoLabel c e Q D ũ hQ hD

end PredGeneric

/-! ## The certificate -/

section Cert

variable [HasPrg]

/-- The check value of the chain's committed response, with the chain's `chal1` and `ũ`. -/
noncomputable def chKos (st : Statement) (ch : Chain) (T : CrtTables) : Blocks → Fin 4 → GF128 :=
  kosValue ch.kosCh (lift T) (ch.kosQ st T) (ch.kosD st T) (ch.kosU st)

/-- The class key of a tree: its witness rows and its label rows. -/
def clsKey (st : Statement) (ch : Chain) (i : Fin BAVC.tau) :
    (Fin st.params.witnessBits → Bool) × (Fin 128 → Bool) :=
  (ch.u st i, ch.lab st i)

lemma clsKey_eq_iff (st : Statement) (ch : Chain) (i i' : Fin BAVC.tau) :
    clsKey st ch i = clsKey st ch i' ↔ ch.u st i = ch.u st i' ∧ ch.lab st i = ch.lab st i' :=
  Prod.ext_iff

/-- **The decoder's certificate for the class of tree `i`**, for the check value `K`, the alive
trees `S` and the blocks `hd` of the other trees: a direction supported on tree `i`, a base point
and a set of generators whose predicted increment of `K` is `0`. -/
def clsCertK (K : Blocks → Fin 4 → GF128) (st : Statement) (ch : Chain)
    (S : Finset (Fin BAVC.tau)) (hd : Blocks) (i : Fin BAVC.tau) : Prop :=
  ∃ t, decCand K ((treeDirs i).erase 0)
    (basePts (sliceOf S hd) (clsOf S (clsKey st ch) i)
      (clsT1 S (clsKey st ch) (ch.lab st) i))
    (genOf (clsT1 S (clsKey st ch) (ch.lab st) i)) t

/-- The certificate for the chain's own check value. -/
def clsCert (st : Statement) (ch : Chain) (T : CrtTables) (S : Finset (Fin BAVC.tau))
    (hd : Blocks) (i : Fin BAVC.tau) : Prop :=
  clsCertK (chKos st ch T) st ch S hd i

/-- The points at which the certificate reads the check value. -/
noncomputable def clsPts (st : Statement) (ch : Chain) (S : Finset (Fin BAVC.tau)) (hd : Blocks)
    (i : Fin BAVC.tau) : Finset Blocks :=
  decPts ((treeDirs i).erase 0)
    (basePts (sliceOf S hd) (clsOf S (clsKey st ch) i)
      (clsT1 S (clsKey st ch) (ch.lab st) i))
    (genOf (clsT1 S (clsKey st ch) (ch.lab st) i))

/-- **The certificate reads the check value at `clsPts` only.** -/
theorem clsCertK_congr {K K' : Blocks → Fin 4 → GF128} (st : Statement) (ch : Chain)
    (S : Finset (Fin BAVC.tau)) (hd : Blocks) (i : Fin BAVC.tau)
    (h : ∀ x ∈ clsPts st ch S hd i, K' x = K x) :
    clsCertK K' st ch S hd i ↔ clsCertK K st ch S hd i := by
  unfold clsCertK
  refine exists_congr fun t => ?_
  unfold decCand
  refine and_congr_right fun h1 => and_congr_right fun h2 => ?_
  rw [decPred_congr h h1 h2]

/-- **The number of evaluations of the certificate**: `|U|·|Rs|·2(n + 1)`, with at most `2⁸ − 1`
directions and `n = 120` generators. -/
theorem card_clsPts_le (st : Statement) (ch : Chain) (S : Finset (Fin BAVC.tau)) (hd : Blocks)
    (i : Fin BAVC.tau) :
    (clsPts st ch S hd i).card ≤ (2 ^ 8 - 1) *
      (∏ k ∈ S \ (clsOf S (clsKey st ch) i ∪ clsT1 S (clsKey st ch) (ch.lab st) i),
        Fintype.card (Fin (BAVC.kOf k) → ZMod 2)) * (2 * (nGen + 1)) := by
  classical
  refine (card_decPts_le _ _ _).trans ?_
  refine Nat.mul_le_mul_right _ (Nat.mul_le_mul ?_ (card_basePts_le S _ _ hd))
  have h0 : (0 : Blocks) ∈ treeDirs i := mem_treeDirs.2 fun _ _ => rfl
  rw [Finset.card_erase_of_mem h0, card_treeDirs]
  exact Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) (width_le_eight i)) 1

omit [HasPrg] in
/-- The decoder's data: the hypotheses on the points in `dec_cert_sound` and
`dec_cert_complete` (`basePts_cover` with the generators `genOf`). -/
theorem cls_cover (S C T₁ : Finset (Fin BAVC.tau)) (hd : Blocks) (hC : C ⊆ S) (hT : T₁ ⊆ S) :
    (∀ r ∈ basePts (sliceOf S hd) C T₁, r ∈ sliceOf S hd) ∧
      (∀ δ ∈ dirs (B := fun i : Fin BAVC.tau => Fin (BAVC.kOf i) → ZMod 2) C,
        ∀ r ∈ basePts (sliceOf S hd) C T₁, ∀ s,
          decPt (genOf T₁) r s ∈ sliceOf S hd ∧ decPt (genOf T₁) r s + δ ∈ sliceOf S hd) ∧
      (∀ x ∈ sliceOf S hd, ∀ δ ∈ dirs (B := fun i : Fin BAVC.tau => Fin (BAVC.kOf i) → ZMod 2) C,
        x + δ ∈ sliceOf S hd) ∧
      ∀ Δ ∈ sliceOf S hd, ∃ r ∈ basePts (sliceOf S hd) C T₁, ∃ s,
        decPt (genOf T₁) r s ∈ sliceOf S hd ∧ ∀ i ∉ C, decPt (genOf T₁) r s i = Δ i :=
  basePts_cover S C T₁ hd hC hT (genOf_mem_dirs T₁) (genOf_span T₁)

/-- The two-label structure of the response for the class of `i` and `clsT1`. -/
lemma cls_twoLabelOn (st : Statement) (ch : Chain) (T : CrtTables)
    (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    (S : Finset (Fin BAVC.tau)) (i : Fin BAVC.tau) (Sb : Set Blocks) :
    TwoLabelOn Sb (clsOf S (clsKey st ch) i) (clsT1 S (clsKey st ch) (ch.lab st) i)
      (ch.kosQ st T) (ch.kosD st T) :=
  chain_twoLabelOn st ch T hlab (clsOf_disjoint_clsT1 _ _ _ _)
    (fun k hk k' hk' => by
      have h1 := ((clsKey_eq_iff st ch _ _).1 (mem_clsOf.1 hk).2).2
      have h2 := ((clsKey_eq_iff st ch _ _).1 (mem_clsOf.1 hk').2).2
      rw [h1, h2])
    (fun k hk k' hk' => by
      rw [(mem_clsT1.1 hk).2.2, (mem_clsT1.1 hk').2.2]) Sb

/-- **A candidate of the decoder is a pair** (for the executable verifier the prediction is
exact): the certificate holds iff the decoder of `Seed/SliceDecode.lean` outputs a pair. -/
theorem clsCert_iff_dec (st : Statement) (ch : Chain) (T : CrtTables)
    (hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows)
    (S : Finset (Fin BAVC.tau)) (hd : Blocks) {i : Fin BAVC.tau} (hiS : i ∈ S) :
    clsCert st ch T S hd i ↔
      (dec (chKos st ch T) ((treeDirs i).erase 0)
        (basePts (sliceOf S hd) (clsOf S (clsKey st ch) i)
          (clsT1 S (clsKey st ch) (ch.lab st) i))
        (genOf (clsT1 S (clsKey st ch) (ch.lab st) i))).isSome := by
  classical
  obtain ⟨hRs, -, -, -⟩ := cls_cover S (clsOf S (clsKey st ch) i)
    (clsT1 S (clsKey st ch) (ch.lab st) i) hd (Finset.filter_subset _ S)
    (Finset.filter_subset _ S)
  exact exists_decCand_iff_dec (decPred_exact_of_twoLabel ch.kosCh (lift T) (ch.kosU st)
    (cls_twoLabelOn st ch T hlab S i (sliceOf S hd))
    (fun δ hδ => treeDirs_dirs (self_mem_clsOf hiS) (Finset.mem_of_mem_erase hδ))
    (genOf_mem_dirs _) hRs)

end Cert

/-! ## The per-chain step for the executable verifier -/

section Chain

variable [HasPrg]

omit [HasPrg] in
lemma pomfrit_hlab (lr : Bool) :
    (pomfritParams lr).labelRowOffset + 128 ≤ (pomfritParams lr).correctionRows := by
  cases lr <;> decide

open Classical in
/-- **Lemma P^cls at a chain of the executable verifier** (`pomfritT_extract_major_chain` with the
class extractor and `2⁵⁰`): for a statement with PomFRIT's parameters whose constraint evaluator
is PomFRIT's system at a target `h` and a combination `l`, a `chal1` that is KOS-good on `Sb` and
good for parallelism, and an accepting set `A` whose blocks outside `S` are `hd`: some tree of `S`
has a candidate encoding `(ρ, σ)` with `P(σ) = h + ρ` whose prefix `pf` is the output of the class
extractor (classes by witness and label rows, certificates `clsCert`), or at most `2⁵⁰`
admissible `chal3` are accepted. -/
theorem pomfritT_extract_class_chain {Ch : Type*} {P : Type*} [DecidableEq P] (pk : UovPk)
    (st : Statement) (lr : Bool) (hp : st.params = pomfritParams lr) (ch : Chain)
    (h : Fin 45 → GF256) (l : Fin 45 → GF128)
    (hvals : ∀ x, ch.vals x =
      (PomFRIT.pomfritRedeemSystem beta GF256.toBits 119 45 pk.map h l).values x)
    {A : Finset Blocks} (hA : ∀ Δ ∈ A, ch.OnChain st CrtGen.tables Δ) {Sb : Set Blocks}
    (hAS : (A : Set Blocks) ⊆ Sb)
    (hkos : Seed.KOSGood ch.kosCh Sb (lift CrtGen.tables) (ch.kosQ st CrtGen.tables)
      (ch.kosD st CrtGen.tables))
    (hpar : Seed.KOSPar ch.kosCh (DisjQuads fun i : Fin BAVC.tau => Fin (BAVC.kOf i) → ZMod 2)
      (lift CrtGen.tables) (ch.kosQ st CrtGen.tables) (ch.kosD st CrtGen.tables))
    {S : Finset (Fin BAVC.tau)} (hd : Blocks) (hdead : ∀ Δ ∈ A, ∀ i ∉ S, Δ i = hd i)
    (hQS : 2 ≤ A.card → ∀ uStar, (∀ j, ∃ v, ∀ Δ ∈ A,
        ch.Qw st CrtGen.tables j Δ = v + uStar j * lift CrtGen.tables Δ) →
      ¬(PomFRIT.pomfritRedeemSystem beta GF256.toBits 119 45 pk.map h l).Holds
        (wStar uStar (ch.dc st)) →
      Seed.zkHash _ (gfOfBytes ch.chal2 0) (gfOfBytes ch.chal2 16) (gfOfBytes ch.chal2 32)
        ⟨W128.word ch.chal2 48, 0⟩
        (valVec (PomFRIT.pomfritRedeemSystem beta GF256.toBits 119 45 pk.map h l)
          (wStar uStar (ch.dc st))) ≠ 0)
    (hcomb : 2 ≤ A.card → ∀ uStar, (∀ j, ∃ v, ∀ Δ ∈ A,
        ch.Qw st CrtGen.tables j Δ = v + uStar j * lift CrtGen.tables Δ) →
      (PomFRIT.pomfritRedeemSystem beta GF256.toBits 119 45 pk.map h l).Holds
        (wStar uStar (ch.dc st)) →
      pomfritWit GF256.ofBits 119 45 pk.map h (wStar uStar (ch.dc st)))
    (pf : (ℕ → GF128) → P)
    (Z : Finset Ch) (δ : Ch → Blocks) (hδ : Set.InjOn δ Z) (acc : Ch → Prop) [DecidablePred acc]
    (hclaim1 : ∀ x ∈ Z, acc x → δ x ∈ A) :
    (∃ i ∈ S, pomfritWit GF256.ofBits 119 45 pk.map h
        (candidate (F := GF128) (ch.u st) (ch.dc st) i) ∧
        clsExt S (clsKey st ch) (fun i => pf (candidate (F := GF128) (ch.u st) (ch.dc st) i))
            (fun i => clsCert st ch CrtGen.tables S hd i) =
          some (pf (candidate (F := GF128) (ch.u st) (ch.dc st) i))) ∨
      #{x ∈ Z | acc x} ≤ 2 ^ 50 := by
  by_cases hA1 : A.card ≤ 1
  · exact Or.inr (few_of_card_le_one hA1 Z δ hδ acc hclaim1 (by norm_num))
  have hlab : st.params.labelRowOffset + 128 ≤ st.params.correctionRows := by
    rw [hp]; exact pomfrit_hlab lr
  have hL2 : ∀ i ∉ S, IsFixed (A : Set Blocks) i := fun i hi Δ hΔ Δ' hΔ' => by
    rw [hdead Δ hΔ i hi, hdead Δ' hΔ' i hi]
  have hASd : (A : Set Blocks) ⊆ (sliceOf S hd) := fun Δ hΔ => hdead Δ hΔ
  obtain ⟨lStar, hKL⟩ := chain_claim4_lab liftInvOk_tables st ch hlab hA hAS hkos hL2
  have hℓL : st.params.witnessBits ≤ Chain.kosL st := by
    have := witnessBits_le st.params
    unfold Chain.kosL; omega
  have hQeq : (fun (j : Fin st.params.witnessBits) (Δ : Blocks) =>
      ch.kosQ st CrtGen.tables Δ (Fin.castLE hℓL j)) = ch.Qw st CrtGen.tables := by
    funext j Δ
    exact ch.kosQ_row st CrtGen.tables Δ (lt_of_lt_of_le j.isLt (witnessBits_le _))
  have haccK : ∀ Δ ∈ A, chKos st ch CrtGen.tables Δ = fun j : Fin 4 => ch.hV[(j : ℕ)]! :=
    fun Δ hΔ => kos_onChain st ch CrtGen.tables (hA Δ hΔ)
  have htree : ∀ j : Fin st.params.witnessBits, ∃ c', ∀ Δ ∈ (sliceOf S hd),
      ch.kosQ st CrtGen.tables Δ (Fin.castLE hℓL j) = c' + ∑ i ∈ S,
        SeedExtraction.bit (ch.u st i j) * blockLift (lift CrtGen.tables) i (Δ i) := by
    intro j
    obtain ⟨c', hc'⟩ := ch.row_tree_form st CrtGen.tables
      (A := (sliceOf S hd)) (known := S)
      (fun i hi Δ hΔ Δ' hΔ' => by rw [hΔ i hi, hΔ' i hi])
      (lt_of_lt_of_le j.isLt (witnessBits_le _))
    exact ⟨c', fun Δ hΔ =>
      (ch.kosQ_row st CrtGen.tables Δ (lt_of_lt_of_le j.isLt (witnessBits_le _))).trans
        (hc' Δ hΔ)⟩
  have hdeg2 : st.params.qsDegree = 2 := by rw [hp]; rfl
  obtain ⟨uStar, R, hR, hK, hacc⟩ := chain_claim4 liftInvOk_tables st ch _ hvals
    (by rw [hdeg2]; exact PomFRIT.degree_pomfritRedeemSystem _ _ _ _ _ _ _) hA hAS hkos hL2
  rw [hdeg2] at hR hacc
  refine extract_or_class (d := 2) (by norm_num) (by norm_num) card_block hK hKL _ _
    (PomFRIT.degree_pomfritRedeemSystem _ _ _ _ _ _ _) (pomfritWit GF256.ofBits 119 45 pk.map h)
    (fun w hw j hj => bits_of_exists_bitF w hw j (by
      have : st.params.witnessBits = 8 * 164 := by rw [hp]; rfl
      rw [this] at hj; exact hj)) _ R hR hacc
    (fun hh => by rw [← Seed.zkHash_eq_sum]; exact hQS (by omega) uStar hK.consistent hh)
    (hcomb (by omega) uStar hK.consistent) pf (clsKey st ch) (clsKey_eq_iff st ch) _
    (fun hbits hfree i hi hcert => ?_) (fun i hi hw hw57 hfix hgt => ?_) Z δ hδ acc hclaim1
  · -- Soundness: a candidate is a pair of the decoder, and a pair is a certificate.
    obtain ⟨i₀, hfree⟩ := hfree
    obtain ⟨-, hSb, -, -⟩ := cls_cover S (clsOf S (clsKey st ch) i)
      (clsT1 S (clsKey st ch) (ch.lab st) i) hd (Finset.filter_subset _ S)
      (Finset.filter_subset _ S)
    have hK' := hK
    rw [← hQeq] at hK'
    exact dec_cert_sound hℓL hpar _ _ haccK hK' hbits hfree htree (Finset.filter_subset _ S)
      (C := clsOf S (clsKey st ch) i) (uC := ch.u st i) (fun k hk j => by
        rw [((clsKey_eq_iff st ch _ _).1 (mem_clsOf.1 hk).2).1])
      (fun δ hδ => ⟨Finset.ne_of_mem_erase hδ,
        treeDirs_dirs (self_mem_clsOf hi) (Finset.mem_of_mem_erase hδ)⟩)
      (fun δ hδ r hr s => hSb δ (treeDirs_dirs (self_mem_clsOf hi)
        (Finset.mem_of_mem_erase hδ)) r hr s)
      ((clsCert_iff_dec st ch CrtGen.tables hlab S hd hi).1 hcert)
  · -- Completeness: `2⁷·|A| > 2⁵⁷ ≥ ∏_{C} |B_i|`.
    obtain ⟨hRs, -, hSbD, hcov⟩ := cls_cover S (clsOf S (clsKey st ch) i)
      (clsT1 S (clsKey st ch) (ch.lab st) i) hd (Finset.filter_subset _ S)
      (Finset.filter_subset _ S)
    refine (clsCert_iff_dec st ch CrtGen.tables hlab S hd hi).2 ?_
    refine dec_cert_complete _ _
      (fun x => funext fun k => funext fun b => CharTwo.add_self_eq_zero (x k b)) hASd haccK hfix hSbD
      (fun g => chain_affineOn st ch CrtGen.tables hlab (fun k hk k' hk' => by
        have h1 := ((clsKey_eq_iff st ch _ _).1 (mem_clsOf.1 hk).2).2
        have h2 := ((clsKey_eq_iff st ch _ _).1 (mem_clsOf.1 hk').2).2
        rw [h1, h2]) S hd g)
      (cls_twoLabelOn st ch CrtGen.tables hlab S i _)
      (fun a ha b hb => treeDirs_add ha hb)
      (fun δ hδ => treeDirs_dirs (self_mem_clsOf hi) hδ)
      (genOf_mem_dirs _) hRs hcov ?_
    have hprod : ∏ k ∈ clsOf S (clsKey st ch) i,
        Fintype.card (Fin (BAVC.kOf k) → ZMod 2) ≤ 2 ^ 57 :=
      ((Finset.prod_congr rfl fun k _ => card_block k).trans
        (Finset.prod_pow_eq_pow_sum (clsOf S (clsKey st ch) i) (fun k => width k) 2)).le.trans
        (Nat.pow_le_pow_right (by norm_num) hw57)
    calc ∏ k ∈ clsOf S (clsKey st ch) i, Fintype.card (Fin (BAVC.kOf k) → ZMod 2) ≤ 2 ^ 57 := hprod
      _ = 2 ^ 7 * 2 ^ 50 := by norm_num
      _ < 2 ^ 7 * A.card := Nat.mul_lt_mul_of_pos_left hgt (by norm_num)
      _ ≤ (treeDirs i).card * A.card := Nat.mul_le_mul_right _
          (le_of_le_of_eq (Nat.pow_le_pow_right (by norm_num) (seven_le_width i))
            (card_treeDirs i).symm)

end Chain

end VoleMole.PomFRIT
